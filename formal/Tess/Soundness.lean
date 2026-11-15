import Tess.Check
import Mathlib.Tactic
namespace Tess

/-! Proved consequences of acceptance of the decoded artifact. These intermediate facts feed the real-domain coverage and continuous
lifting theorems. -/
structure StructuralValid (request cert : Certificate) : Prop where
  requestBound : request.requestedAxis=cert.requestedAxis ∧
    request.strictPlanar=cert.strictPlanar ∧ request.rings=cert.rings ∧
    request.seed.points=cert.seed.points
  frozenSeed : request.seed=cert.seed
  seedPositive : ∀ f ∈ cert.seed.faces,
    0 < orient (cert.seed.project f.a) (cert.seed.project f.b) (cert.seed.project f.c)
  outputPositive : ∀ f ∈ cert.output.faces,
    0 < orient (cert.output.project f.a) (cert.output.project f.b) (cert.output.project f.c)
  outputBoundary : ∀ e ∈ faceEdges cert.output ++ orientedBoundary cert.rings cert.output,
    balance (faceEdges cert.output) e.1 e.2 = balance (orientedBoundary cert.rings cert.output) e.1 e.2
  fixedInput : ∀ i < cert.seed.points.size,
    cert.seed.point i = cert.output.point i
  overlayEquality : ∀ a ∈ cert.seed.faces, ∀ b ∈ cert.output.faces,
    ∀ p ∈ overlayPoints cert.seed a cert.output b,
      affineHeight cert.seed a p = affineHeight cert.output b p

private theorem positive_of_meshCheck (rings : Array Nat) (m : ExactMesh)
    (h : meshCheck rings m = true) :
    ∀ f ∈ m.faces, 0 < orient (m.project f.a) (m.project f.b) (m.project f.c) := by
  simp only [meshCheck, Bool.and_eq_true] at h
  have hp : m.faces.all (facePositive m) = true := by aesop
  intro f hf
  have hv := (Array.all_eq_true'.mp hp) f hf
  have hpositive : positive (m.project f.a) (m.project f.b) (m.project f.c) = true := by
    simp only [facePositive, Bool.and_eq_true] at hv
    exact hv.2
  exact positive_sound _ _ _ hpositive

theorem check_structural_sound (request cert : Certificate)
    (accepted : check request cert = true) : StructuralValid request cert := by
  simp only [check, Bool.and_eq_true] at accepted
  have hreq : sameRequest request cert = true := by aesop
  have hs : meshCheck cert.rings cert.seed = true := by aesop
  have ho : meshCheck cert.rings cert.output = true := by aesop
  have hc : constraintCheck cert = true := by aesop
  have hr : referenceCheck cert.seed cert.output = true := by aesop
  constructor
  · simp only [sameRequest,decide_eq_true_eq] at hreq
    exact hreq.1
  · simp only [sameRequest,decide_eq_true_eq] at hreq
    exact hreq.2
  · exact positive_of_meshCheck _ _ hs
  · exact positive_of_meshCheck _ _ ho
  · have hb : boundaryCheckEdges (ringEdges cert.rings) cert.output=true := by
      simp only [meshCheck,Bool.and_eq_true] at ho
      exact ho.1.2
    simpa only [boundaryCheckEdges,List.all_eq_true,decide_eq_true_eq,orientedBoundary] using hb
  · simp only [constraintCheck, Bool.and_eq_true, allN, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
    aesop
  · simp only [referenceCheck, Bool.and_eq_true] at hr
    simpa only [overlayCheck, Array.all_eq_true', List.all_eq_true, decide_eq_true_eq] using hr.1
#print axioms check_structural_sound
end Tess
