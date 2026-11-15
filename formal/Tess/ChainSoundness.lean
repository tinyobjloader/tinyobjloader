import Tess.V2Check
import Tess.Subdivision
import Tess.CertificateCoverage
noncomputable section
namespace Tess
open RealGeometry

theorem coord_pointAt (a b : Point3) (t : Rat) (axis : Nat) :
    (pointAt a b t).coord axis=a.coord axis+t*(b.coord axis-a.coord axis) := by
  unfold Point3.coord
  split_ifs <;> rfl

theorem pointAt_project_real (seed output : ExactMesh) (original : Constraint)
    (i : Nat) (t : Rat) (axes : seed.u=output.u ∧ seed.w=output.w)
    (h : output.point i=pointAt (seed.point original.a) (seed.point original.b) t) :
    realPoint output i=interpolate (realPoint seed original.a) (realPoint seed original.b) (t : ℝ) := by
  simp only [realPoint,ExactMesh.project,h,coord_pointAt,← axes.1,← axes.2,interpolate]
  push_cast
  rfl

def realChain (segments : List Constraint) : List (Nat × Nat × ℝ × ℝ) :=
  segments.map fun e => (e.a,e.b,(e.ta : ℝ),(e.tb : ℝ))

theorem chainFrom_parameters (seed output : ExactMesh) (original : Constraint)
    (segments : List Constraint) (v : Nat) (t : Rat)
    (axes : seed.u=output.u ∧ seed.w=output.w)
    (checked : chainFrom seed output original v t segments=true) :
    parameterChain (realPoint seed original.a) (realPoint seed original.b) (realPoint output)
      v (t : ℝ) original.b (realChain segments) := by
  induction segments generalizing v t with
  | nil =>
    simp only [chainFrom,decide_eq_true_eq] at checked
    simp only [realChain,List.map_nil,parameterChain]
    exact ⟨checked.1,by exact_mod_cast checked.2⟩
  | cons e tail ih =>
    simp only [chainFrom,Bool.and_eq_true,decide_eq_true_eq] at checked
    rcases checked.1 with ⟨av,tv,order,upper,kind,source,owner,tag,abound,bbound,distinct,pa,pb⟩
    simp only [realChain,List.map_cons,parameterChain]
    refine ⟨av,by exact_mod_cast tv,by exact_mod_cast order,by exact_mod_cast upper,
      pointAt_project_real seed output original e.a e.ta axes pa,
      pointAt_project_real seed output original e.b e.tb axes pb,?_⟩
    exact ih e.b e.tb checked.2

/-- Exact 3D affine endpoint checks, ordered parameters and matching IDs prove
preservation of each constrained chain's oriented winding. Tags and permission
checks remain separate executable conjuncts in `extendedConstraints`. -/
theorem chainFrom_winding (seed output : ExactMesh) (original : Constraint)
    (segments : List Constraint) (axes : seed.u=output.u ∧ seed.w=output.w)
    (checked : chainFrom seed output original original.a 0 segments=true)
    (p : P2) (generic : ∀ e∈segments, (realPoint output e.a).2≠p.2 ∧ (realPoint output e.b).2≠p.2)
    (ga : (realPoint seed original.a).2≠p.2) (gb : (realPoint seed original.b).2≠p.2) :
    (segments.map (fun e => edgeRay (realPoint output e.a) (realPoint output e.b) p)).sum=
      edgeRay (realPoint seed original.a) (realPoint seed original.b) p := by
  have chain:=chainFrom_parameters seed output original segments original.a 0 axes checked
  have genericReal : ∀ e∈realChain segments, (realPoint output e.1).2≠p.2 ∧ (realPoint output e.2.1).2≠p.2 := by
    intro e he
    obtain ⟨segment,hs,rfl⟩:=List.mem_map.mp he
    exact generic segment hs
  have equal:=parameterChain_ray _ _ p (realPoint output) (realChain segments) original.b original.a 0
    (by simpa using chain) genericReal
  rw [edgeRay_endpoints _ _ _ ga gb]
  simpa [realChain,List.map_map,Function.comp_def] using equal

theorem chainFrom_kinds (seed output : ExactMesh) (original : Constraint)
    (segments : List Constraint) (v : Nat) (t : Rat)
    (checked : chainFrom seed output original v t segments=true) :
    ∀ e∈segments, e.kind=original.kind := by
  induction segments generalizing v t with
  | nil => simp
  | cons e tail ih =>
    simp only [chainFrom,Bool.and_eq_true,decide_eq_true_eq] at checked
    rcases checked.1 with ⟨av,tv,order,upper,kind,rest⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hq
    · exact kind
    · exact ih e.b e.tb checked.2 q hq

private theorem sum_flatMap_int {α : Type} (xs : List α) (f : α → List ℤ) :
    (xs.flatMap f).sum=(xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => simp
  | cons x tail ih => simp [List.sum_append,ih]

private theorem filter_kind_one (segments : List Constraint) (kinds : ∀ e∈segments,e.kind=1) :
    segments.filterMap (fun e => if e.kind=1 then some (e.a,e.b) else none)=
      segments.map (fun e => (e.a,e.b)) := by
  induction segments with
  | nil => simp
  | cons e tail ih =>
    simp only [List.filterMap_cons,List.map_cons,kinds e (by simp),ite_true]
    congr 1
    exact ih (fun q hq => kinds q (by simp [hq]))

theorem check2_boundary_winding (request cert : Certificate2) (accepted : check2 request cert=true)
    (p : P2)
    (seedGeneric : ∀ e∈cert.snapshot.seed.constraints, (realPoint cert.snapshot.seed e.a).2≠p.2 ∧
      (realPoint cert.snapshot.seed e.b).2≠p.2)
    (outputGeneric : ∀ e∈cert.snapshot.output.constraints, (realPoint cert.snapshot.output e.a).2≠p.2 ∧
      (realPoint cert.snapshot.output e.b).2≠p.2) :
    ((expandedBoundary cert).map (fun (a,b) => edgeRay (realPoint cert.snapshot.output a)
      (realPoint cert.snapshot.output b) p)).sum =
    ((ringEdges cert.snapshot.rings).map (fun (a,b) => edgeRay (realPoint cert.snapshot.seed a)
      (realPoint cert.snapshot.seed b) p)).sum := by
  have hc : extendedConstraints cert=true := by
    simp only [check2,Bool.and_eq_true] at accepted; aesop
  have axes : cert.snapshot.seed.u=cert.snapshot.output.u ∧ cert.snapshot.seed.w=cert.snapshot.output.w := by
    simp only [check2,Bool.and_eq_true,decide_eq_true_eq] at accepted; aesop
  simp only [extendedConstraints,Bool.and_eq_true] at hc
  have owners := hc.2
  have seedAll := hc.1.1.2
  unfold expandedBoundary
  rw [List.map_flatMap,sum_flatMap_int]
  apply congrArg List.sum
  apply List.map_congr_left
  intro edge he
  rcases edge with ⟨ea,eb⟩
  have existsOwner := (List.all_eq_true.mp owners) (ea,eb) he
  simp only [Array.any_eq_true',decide_eq_true_eq] at existsOwner
  obtain ⟨original,ho,ha,hb,hkind,howner⟩:=existsOwner
  have seedChecked := Array.all_eq_true'.mp seedAll original ho
  simp only [Bool.and_eq_true] at seedChecked
  have chainChecked : chainFrom cert.snapshot.seed cert.snapshot.output original original.a 0
      (ownerSegments cert.snapshot.output original.owner)=true := by
    have chain:=seedChecked.2
    simp [hkind] at chain
    exact chain.1
  have kinds:=chainFrom_kinds _ _ original _ _ _ chainChecked
  have filtered : (ownerSegments cert.snapshot.output ea).filterMap
      (fun e => if e.kind=1 then some (e.a,e.b) else none) =
      (ownerSegments cert.snapshot.output original.owner).map (fun e => (e.a,e.b)) := by
    rw [← howner]
    exact filter_kind_one _ (fun e he => (kinds e he).trans hkind)
  dsimp only
  rw [filtered,List.map_map]
  have genOriginal:=seedGeneric original ho
  have genSegment : ∀ e∈ownerSegments cert.snapshot.output original.owner,
      (realPoint cert.snapshot.output e.a).2≠p.2 ∧ (realPoint cert.snapshot.output e.b).2≠p.2 := by
    intro e he
    exact outputGeneric e (by simpa using (List.mem_filter.mp he).1)
  simpa only [ha,hb,Function.comp_def] using
    chainFrom_winding _ _ original _ axes chainChecked p genSegment genOriginal.1 genOriginal.2

#print axioms chainFrom_winding
end Tess
