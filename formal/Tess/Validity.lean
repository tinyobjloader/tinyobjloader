import Tess.ReferenceSoundness
noncomputable section
namespace Tess
open RealGeometry Set

/-- Mathematical validity for the version-1 fixed-boundary, exact-reference
certificate. Optimizer quality, deterministic seed replay, parser correctness,
and machine-code refinement are deliberately separate claims. -/
structure Valid (request cert : Certificate) : Prop where
  structural : StructuralValid request cert
  coverage : windingDomain (requestPoint request cert) (ringEdges request.rings) = meshDomain cert.output
  seedComplex : ∀ i (hi : i<cert.seed.faces.size) j (hj : j < i),
    faceRegion cert.seed cert.seed.faces[i] ∩ faceRegion cert.seed cert.seed.faces[j] =
      commonSimplex (realPoint cert.seed) cert.seed.faces[i] cert.seed.faces[j]
  outputComplex : ∀ i (hi : i<cert.output.faces.size) j (hj : j < i),
    faceRegion cert.output cert.output.faces[i] ∩ faceRegion cert.output cert.output.faces[j] =
      commonSimplex (realPoint cert.output) cert.output.faces[i] cert.output.faces[j]
  seedGraph : Nonempty ({p // p∈meshDomain cert.seed} ≃ₜ {q // q∈surface cert.seed})
  outputGraph : Nonempty ({p // p∈meshDomain cert.output} ≃ₜ {q // q∈surface cert.output})
  exactReference : EqOn (globalHeight cert.seed) (globalHeight cert.output) (meshDomain cert.output)
  preservedSurface : surface cert.seed=surface cert.output
  preservedConstraints : cert.seed.constraints=cert.output.constraints

theorem check_sound (request cert : Certificate) : check request cert=true → Valid request cert := by
  intro accepted
  have seedChecked : meshCheck cert.rings cert.seed=true := by
    simp only [check,Bool.and_eq_true] at accepted; aesop
  have outputChecked : meshCheck cert.rings cert.output=true := by
    simp only [check,Bool.and_eq_true] at accepted; aesop
  have constraints : constraintCheck cert=true := by
    simp only [check,Bool.and_eq_true] at accepted; aesop
  have reference := check_exact_reference request cert accepted
  have domainEq := seed_output_domain request cert accepted
  have surfaceEq : surface cert.seed=surface cert.output := by
    rw [surface_eq_graph cert.rings cert.seed seedChecked,surface_eq_graph cert.rings cert.output outputChecked]
    ext q
    change (q.1∈meshDomain cert.seed ∧ q.2=globalHeight cert.seed q.1) ↔
      (q.1∈meshDomain cert.output ∧ q.2=globalHeight cert.output q.1)
    rw [domainEq]
    by_cases hp : q.1∈meshDomain cert.output
    · simp only [hp,true_and,reference hp]
    · simp [hp]
  refine ⟨check_structural_sound request cert accepted,check_request_coverage request cert accepted,
    (fun i hi j hj => mesh_intersection_sound cert.rings cert.seed seedChecked i j hi hj),
    (fun i hi j hj => mesh_intersection_sound cert.rings cert.output outputChecked i j hi hj),
    ⟨graphHomeomorph cert.rings cert.seed seedChecked⟩,
    ⟨graphHomeomorph cert.rings cert.output outputChecked⟩,reference,surfaceEq,?_⟩
  simp only [constraintCheck,Bool.and_eq_true,decide_eq_true_eq] at constraints
  aesop
#print axioms check_sound
end Tess
