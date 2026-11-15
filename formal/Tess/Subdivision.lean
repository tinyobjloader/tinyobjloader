import Tess.Winding
noncomputable section
namespace Tess.RealGeometry

/-- Splitting an oriented segment at an interior affine parameter preserves its
ray contribution away from the supporting and horizontal lines. -/
theorem rayDelta_split (a b m x : ℝ) (t : ℝ)
    (ht : 0<t) (ht1 : t<1) (hm : m=(1-t)*a+t*b)
    (ha : a≠0) (hb : b≠0) (hmid : m≠0) (hx : x≠0) :
    rayDelta a m (t*x) + rayDelta m b ((1-t)*x) = rayDelta a b x := by
  have ht' : 0<1-t := by linarith
  have same1 : (0<t*x ↔ 0<x) := mul_pos_iff_of_pos_left ht
  have same2 : (t*x<0 ↔ x<0) := by constructor <;> intro h <;> nlinarith
  have same3 : (0<(1-t)*x ↔ 0<x) := mul_pos_iff_of_pos_left ht'
  have same4 : ((1-t)*x<0 ↔ x<0) := by constructor <;> intro h <;> nlinarith
  have between : min a b ≤ m ∧ m ≤ max a b := by
    rcases le_total a b with hab|hba
    · simp only [min_eq_left hab,max_eq_right hab]
      constructor <;> nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hab),
        mul_nonneg ht'.le (sub_nonneg.mpr hab)]
    · simp only [min_eq_right hba,max_eq_left hba]
      constructor <;> nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hba),
        mul_nonneg ht'.le (sub_nonneg.mpr hba)]
  rcases lt_or_gt_of_ne ha with ha|ha <;>
    rcases lt_or_gt_of_ne hb with hb|hb <;>
    rcases lt_or_gt_of_ne hmid with hm'|hm' <;>
    rcases lt_or_gt_of_ne hx with hx|hx <;>
    simp only [rayDelta,same1,same2,same3,same4] <;>
    simp only [ha,hb,hm',hx,not_lt_of_ge ha.le,not_lt_of_ge hb.le,
      not_lt_of_ge hm'.le,not_lt_of_ge hx.le, and_true,true_and,and_false,false_and,
      ite_true,ite_false,Int.add_zero,Int.zero_add] <;>
      rcases between with ⟨lower,upper⟩ <;>
      simp only [min_le_iff,le_max_iff] at lower upper <;>
      rcases lower with lower|lower <;> rcases upper with upper|upper <;> norm_num at * <;> linarith

def interpolate (a b : P2) (t : ℝ) : P2 :=
  (a.1+t*(b.1-a.1),a.2+t*(b.2-a.2))

theorem edgeRay_split (a b p : P2) (t : ℝ) (ht : 0<t) (ht1 : t<1)
    (ha : a.2≠p.2) (hb : b.2≠p.2) (hm : (interpolate a b t).2≠p.2)
    (hx : orient a b p≠0) :
    edgeRay a (interpolate a b t) p+edgeRay (interpolate a b t) b p=edgeRay a b p := by
  have left : orient a (interpolate a b t) p=t*orient a b p := by
    simp only [orient,interpolate]; ring
  have right : orient (interpolate a b t) b p=(1-t)*orient a b p := by
    simp only [orient,interpolate]; ring
  simp only [edgeRay,left,right]
  exact rayDelta_split _ _ _ _ t ht ht1 (by simp only [interpolate]; ring)
    (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb) (sub_ne_zero.mpr hm) hx

/-- On a monotone supporting line, every subsegment has a common ray
potential. Hence arbitrary ordered subdivisions telescope. -/
def rayPotential (a b side y : ℝ) : ℤ :=
  if (a<b ∧ 0<side) ∨ (b<a ∧ side<0) then (if 0<y then 1 else 0) else 0

theorem rayDelta_potential (a b y z side scale : ℝ)
    (hs : 0<scale) (hy : y≠0) (hz : z≠0)
    (hd : z-y=scale*(b-a)) :
    rayDelta y z (scale*side)=rayPotential a b side z-rayPotential a b side y := by
  have sidePos : 0<scale*side ↔ 0<side := mul_pos_iff_of_pos_left hs
  have sideNeg : scale*side<0 ↔ side<0 := by constructor <;> intro h <;> nlinarith
  have orderPos : y<z ↔ a<b := by
    have fact : 0<scale*(b-a) ↔ 0<b-a := mul_pos_iff_of_pos_left hs
    rw [← hd] at fact
    simpa only [sub_pos] using fact
  have orderNonneg : y≤z ↔ a≤b := by
    have fact : 0≤scale*(b-a) ↔ 0≤b-a := mul_nonneg_iff_of_pos_left hs
    rw [← hd] at fact
    simpa only [sub_nonneg] using fact
  rcases lt_or_gt_of_ne hy with hy|hy
  · rcases lt_or_gt_of_ne hz with hz|hz
    · simp [rayDelta,rayPotential,hy,hz,not_lt_of_ge hy.le,not_lt_of_ge hz.le]
    · have hab : a<b := orderPos.mp (by linarith)
      simp [rayDelta,rayPotential,sidePos,sideNeg,hy,hz,hab,not_lt_of_ge hab.le,
        not_lt_of_ge hy.le,not_lt_of_ge hz.le]
  · rcases lt_or_gt_of_ne hz with hz|hz
    · have hba : b<a := by
        by_contra h
        have := orderNonneg.mpr (le_of_not_gt h)
        linarith
      simp [rayDelta,rayPotential,sidePos,sideNeg,hy,hz,hba,not_lt_of_ge hba.le,
        not_lt_of_ge hy.le,not_lt_of_ge hz.le]
      split_ifs <;> rfl
    · simp [rayDelta,rayPotential,hy,hz,not_lt_of_ge hy.le,not_lt_of_ge hz.le]

theorem edgeRay_potential (a b p : P2) (t s : ℝ) (hts : t<s)
    (hy : (interpolate a b t).2≠p.2) (hz : (interpolate a b s).2≠p.2) :
    edgeRay (interpolate a b t) (interpolate a b s) p =
      rayPotential (a.2-p.2) (b.2-p.2) (orient a b p) ((interpolate a b s).2-p.2) -
      rayPotential (a.2-p.2) (b.2-p.2) (orient a b p) ((interpolate a b t).2-p.2) := by
  have orientation : orient (interpolate a b t) (interpolate a b s) p=(s-t)*orient a b p := by
    simp only [orient,interpolate]; ring
  rw [edgeRay,orientation]
  exact rayDelta_potential _ _ _ _ _ (s-t) (sub_pos.mpr hts)
    (sub_ne_zero.mpr hy) (sub_ne_zero.mpr hz) (by simp only [interpolate]; ring)

def rayValue (a b p : P2) (t : ℝ) : ℤ :=
  rayPotential (a.2-p.2) (b.2-p.2) (orient a b p) ((interpolate a b t).2-p.2)

theorem edgeRay_endpoints (a b p : P2) (ha : a.2≠p.2) (hb : b.2≠p.2) :
    edgeRay a b p=rayValue a b p 1-rayValue a b p 0 := by
  have fact := edgeRay_potential a b p 0 1 (by norm_num)
    (by simpa [interpolate] using ha) (by simpa [interpolate] using hb)
  simpa [rayValue,interpolate] using fact

/-- An abstract ordered parameter chain. Its endpoints are the original
segment endpoints and its ray winding equals the original oriented segment. -/
def parameterChain (a b : P2) (points : Nat → P2) : Nat → ℝ → Nat → List (Nat × Nat × ℝ × ℝ) → Prop
  | v,t,last,[] => v=last ∧ t=1
  | v,t,last,(i,j,s,u)::tail => i=v ∧ s=t ∧ s<u ∧ u≤1 ∧
      points i=interpolate a b s ∧ points j=interpolate a b u ∧
      parameterChain a b points j u last tail

theorem parameterChain_ray (a b p : P2) (points : Nat → P2)
    (edges : List (Nat × Nat × ℝ × ℝ)) (last v : Nat) (t : ℝ)
    (chain : parameterChain a b points v t last edges)
    (generic : ∀ e∈edges, (points e.1).2≠p.2 ∧ (points e.2.1).2≠p.2) :
    (edges.map (fun e => edgeRay (points e.1) (points e.2.1) p)).sum=
      rayValue a b p 1-rayValue a b p t := by
  induction edges generalizing v t with
  | nil => simp only [parameterChain] at chain; simp [chain.2]
  | cons e tail ih =>
    rcases e with ⟨i,j,s,u⟩
    rcases chain with ⟨rfl,rfl,order,upper,hi,hj,rest⟩
    have gen:=generic (i,j,s,u) (by simp)
    have first := edgeRay_potential a b p s u order (by rw [← hi]; exact gen.1)
      (by rw [← hj]; exact gen.2)
    simp only [List.map_cons,List.sum_cons,hi,hj]
    rw [first,ih j u rest (fun e he => generic e (by simp [he]))]
    change (rayValue a b p u-rayValue a b p s)+(rayValue a b p 1-rayValue a b p u)=_
    omega

end Tess.RealGeometry
