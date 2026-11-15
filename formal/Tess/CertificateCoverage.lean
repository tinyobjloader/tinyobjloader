import Tess.DomainCoverage
import Mathlib.Data.Rat.Cast.Order
noncomputable section
namespace Tess
open RealGeometry

def realPoint (m : ExactMesh) (i : Nat) : RealGeometry.P2 :=
  (((m.project i).x : ℝ),((m.project i).y : ℝ))
def requestPoint (request cert : Certificate) (i : Nat) : RealGeometry.P2 :=
  ((((request.seed.point i).coord cert.output.u) : ℝ),(((request.seed.point i).coord cert.output.w) : ℝ))

theorem orient_cast (m : ExactMesh) (a b c : Nat) :
    RealGeometry.orient (realPoint m a) (realPoint m b) (realPoint m c) =
      ((Tess.orient (m.project a) (m.project b) (m.project c)) : ℝ) := by
  simp [realPoint,RealGeometry.orient,Tess.orient]

theorem check_output_coverage (request cert : Certificate) (h : check request cert = true) :
    windingDomain (realPoint cert.output) (ringEdges cert.rings) =
      closedRegion (realPoint cert.output) cert.output.faces.toList := by
  have valid := check_structural_sound request cert h
  apply planar_coverage
  · intro f hf
    rw [orient_cast]
    have positive := valid.outputPositive f (by simpa using hf)
    exact_mod_cast positive
  · have hm : meshCheck cert.rings cert.output = true := by
      simp only [check,Bool.and_eq_true] at h
      aesop
    have hb : boundaryCheck cert.rings cert.output = true := by
      simp only [meshCheck,Bool.and_eq_true] at hm
      aesop
    exact boundary_all_coefficients _ _ hb

theorem ringEdges_bounds (rings : Array Nat) (n : Nat)
    (bounds : ∀ i < rings.size, rings[i]?.getD 0 ≤ n) :
    ∀ e ∈ ringEdges rings, e.1<n ∧ e.2<n := by
  intro e he
  obtain ⟨r,hr,he⟩ := List.mem_flatMap.mp he
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp he
  have hr := List.mem_range.mp hr
  have hk := List.mem_range.mp hk
  have hstop := bounds (r+1) (by omega)
  dsimp only
  constructor
  · omega
  · split_ifs <;> omega

theorem windingDomain_congr_on_edges (edges : List (Nat × Nat)) (p q : Nat → RealGeometry.P2)
    (h : ∀ e ∈ edges, p e.1=q e.1 ∧ p e.2=q e.2) :
    windingDomain p edges = windingDomain q edges := by
  have equal (x : RealGeometry.P2) :
      (edges.map (fun (a,b) => edgeRay (p a) (p b) x)).sum =
      (edges.map (fun (a,b) => edgeRay (q a) (q b) x)).sum := by
    congr 1
    apply List.map_congr_left
    intro e he
    rcases h e he with ⟨ha,hb⟩
    simp only [ha,hb]
  unfold windingDomain
  apply congrArg closure
  apply congrArg interior
  ext x
  simp only [Set.mem_setOf_eq]
  rw [equal x]

/-- Coverage is tied to caller-held input coordinates in the declared chart;
the domain contains no output-mesh coverage assumption. -/
theorem check_request_coverage (request cert : Certificate) (h : check request cert = true) :
    windingDomain (requestPoint request cert) (ringEdges request.rings) =
      closedRegion (realPoint cert.output) cert.output.faces.toList := by
  have valid := check_structural_sound request cert h
  have hd : domainCheck cert.rings cert.seed = true := by
    simp only [check,Bool.and_eq_true] at h
    aesop
  have bounds : allN cert.rings.size (fun r => decide (cert.rings[r]?.getD 0 ≤ cert.seed.points.size)) = true := by
    simp only [domainCheck,Bool.and_eq_true] at hd
    aesop
  simp only [allN,List.all_eq_true,List.mem_range,decide_eq_true_eq] at bounds
  have fixed (i : Nat) (hi : i<cert.seed.points.size) : requestPoint request cert i = realPoint cert.output i := by
    have hp := valid.fixedInput i hi
    have hq : request.seed.point i = cert.seed.point i := by
      simp only [ExactMesh.point,valid.requestBound.2.2.2]
    simp only [requestPoint,realPoint,ExactMesh.project,← hp,← hq]
  rw [valid.requestBound.2.2.1]
  rw [windingDomain_congr_on_edges (ringEdges cert.rings) (requestPoint request cert) (realPoint cert.output)
    (fun e he => ⟨fixed e.1 (ringEdges_bounds _ _ bounds e he).1,fixed e.2 (ringEdges_bounds _ _ bounds e he).2⟩)]
  exact check_output_coverage request cert h


theorem check_seed_coverage (request cert : Certificate) (h : check request cert=true) :
    windingDomain (realPoint cert.seed) (ringEdges cert.rings)=closedRegion (realPoint cert.seed) cert.seed.faces.toList := by
  have valid := check_structural_sound request cert h
  apply planar_coverage
  · intro f hf
    rw [orient_cast]
    have positive := valid.seedPositive f (by simpa using hf)
    exact_mod_cast positive
  · have hm : meshCheck cert.rings cert.seed=true := by
      simp only [check,Bool.and_eq_true] at h; aesop
    have hb : boundaryCheck cert.rings cert.seed=true := by
      simp only [meshCheck,Bool.and_eq_true] at hm; aesop
    exact boundary_all_coefficients _ _ hb

#print axioms check_request_coverage
end Tess
