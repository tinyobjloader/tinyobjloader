import Tess.BoundaryCoverage2
import Tess.ConstraintCoverage
import Tess.ReferenceBoundSoundness
noncomputable section
namespace Tess
open RealGeometry Set

@[simp] theorem globalHeight_geometryView (m : ExactMesh) :
    globalHeight (geometryView m)=globalHeight m := by
  rfl

/-- Euclidean distance in the recorded coordinate permutation (u,w,axis).
The chart uses only permutation/sign normalization, so equal chart coordinates
leave exactly the dropped-coordinate distance. -/
def euclideanDistance (a b : P2 × ℝ) : ℝ :=
  Real.sqrt ((a.1.1-b.1.1)^2+(a.1.2-b.1.2)^2+(a.2-b.2)^2)

def InputPreserved (seed output : ExactMesh) : Prop :=
  (seed.points.size≤output.points.size ∧ seed.vertexIds.size=seed.points.size ∧
    output.vertexIds.size=output.points.size ∧ seed.faceIds.size=seed.faces.size ∧
    output.faceIds.size=output.faces.size ∧ output.vertexIds.toList.Nodup ∧ output.faceIds.toList.Nodup) ∧
  ∀ i<seed.points.size, seed.point i=output.point i ∧ seed.sources[i]?=some i ∧
    output.sources[i]?=some i ∧ seed.pinned[i]?=some true ∧ output.pinned[i]?=some true ∧
    seed.vertexIds[i]?=output.vertexIds[i]?

theorem stableInputCheck_sound (seed output : ExactMesh) (checked : stableInputCheck seed output=true) :
    InputPreserved seed output := by
  simpa only [stableInputCheck,InputPreserved,Bool.and_eq_true,decide_eq_true_eq,
    allN,List.all_eq_true,List.mem_range] using checked

structure Valid2 (request cert : Certificate2) : Prop where
  requestBound : request.snapshot.requestedAxis=cert.snapshot.requestedAxis ∧
    request.snapshot.strictPlanar=cert.snapshot.strictPlanar ∧ request.snapshot.rings=cert.snapshot.rings ∧
    request.snapshot.seed=cert.snapshot.seed ∧ request.run=cert.run
  seedValid : Valid (seedCertificate request) (seedCertificate cert)
  coverage : windingDomain (realPoint request.snapshot.seed) (ringEdges request.snapshot.rings)=meshDomain cert.snapshot.output
  sameDomain : meshDomain cert.snapshot.seed=meshDomain cert.snapshot.output
  outputComplex : ∀ i (hi : i<cert.snapshot.output.faces.size) j (hj : j < i),
    faceRegion cert.snapshot.output cert.snapshot.output.faces[i] ∩ faceRegion cert.snapshot.output cert.snapshot.output.faces[j]=
      commonSimplex (realPoint cert.snapshot.output) cert.snapshot.output.faces[i] cert.snapshot.output.faces[j]
  seedGraph : Nonempty ({p // p∈meshDomain cert.snapshot.seed} ≃ₜ {q // q∈surface cert.snapshot.seed})
  outputGraph : Nonempty ({p // p∈meshDomain cert.snapshot.output} ≃ₜ {q // q∈surface cert.snapshot.output})
  heightBound : ∀ p∈meshDomain cert.snapshot.output,
    |globalHeight cert.snapshot.seed p-globalHeight cert.snapshot.output p|≤(cert.run.tolerance : ℝ)
  exactReference : cert.run.tolerance=0 → EqOn (globalHeight cert.snapshot.seed) (globalHeight cert.snapshot.output)
    (meshDomain cert.snapshot.output)
  constraints : ∀ original∈cert.snapshot.seed.constraints, original.kind≠2 ∨ cert.run.tolerance=0 →
    OrderedConstraintChain cert.snapshot.seed cert.snapshot.output original original.a 0
      (ownerSegments cert.snapshot.output original.owner) ∧
    parameterCover (ownerSegments cert.snapshot.output original.owner)=Icc (0 : ℝ) 1
  forwardDistance : ∀ q∈surface cert.snapshot.seed, ∃ r∈surface cert.snapshot.output,
    q.1=r.1 ∧ euclideanDistance q r≤(cert.run.tolerance : ℝ)
  reverseDistance : ∀ q∈surface cert.snapshot.output, ∃ r∈surface cert.snapshot.seed,
    q.1=r.1 ∧ euclideanDistance q r≤(cert.run.tolerance : ℝ)
  pinnedAndStableInput : InputPreserved cert.snapshot.seed cert.snapshot.output
  fixedConstraints : ∀ original∈cert.snapshot.seed.constraints, original.kind≠2 ∨ cert.run.tolerance=0 →
    permittedSubdivision cert.run original=false → (ownerSegments cert.snapshot.output original.owner).length=1

theorem check2_sound (request cert : Certificate2) (accepted : check2 request cert=true) : Valid2 request cert := by
  have bindings : request.snapshot.requestedAxis=cert.snapshot.requestedAxis ∧
      request.snapshot.strictPlanar=cert.snapshot.strictPlanar ∧ request.snapshot.rings=cert.snapshot.rings ∧
      request.snapshot.seed=cert.snapshot.seed ∧ request.run=cert.run := by
    have h:=accepted
    simp only [check2,Bool.and_eq_true,decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1.1.1.1.1.1,h.1.1.1.1.1.1.1.1.2.1,h.1.1.1.1.1.1.1.1.2.2.1,
      h.1.1.1.1.1.1.1.1.2.2.2.1,h.1.1.1.1.1.1.1.1.2.2.2.2.1⟩
  have seedAccepted:=check2_seed_checked request cert accepted
  have seedChecked : meshCheck cert.snapshot.rings (geometryView cert.snapshot.seed)=true := by
    have h:=seedAccepted
    simp only [check,Bool.and_eq_true] at h
    exact h.1.1.1.1.1.2
  have outputChecked:=check2_output_checked request cert accepted
  have domainEq:=check2_domains request cert accepted
  have referenceChecked : referenceBoundCheck (geometryView cert.snapshot.seed) cert.snapshot.output cert.run.tolerance=true := by
    have h:=accepted
    simp only [check2,Bool.and_eq_true] at h
    exact h.2
  have boundRaw:=referenceBound_sound cert.snapshot.rings (geometryView cert.snapshot.seed) cert.snapshot.output
    cert.run.tolerance seedChecked outputChecked domainEq referenceChecked
  have bound : ∀ p∈meshDomain cert.snapshot.output,
      |globalHeight cert.snapshot.seed p-globalHeight cert.snapshot.output p|≤(cert.run.tolerance : ℝ) := by
    simpa only [globalHeight_geometryView] using boundRaw
  have seedCoverage : windingDomain (realPoint cert.snapshot.seed) (ringEdges cert.snapshot.rings)=meshDomain cert.snapshot.seed :=
    check_seed_coverage (seedCertificate request) (seedCertificate cert) seedAccepted
  have graphSeed : surface cert.snapshot.seed={q : P2×ℝ | q.1∈meshDomain cert.snapshot.seed ∧ q.2=globalHeight cert.snapshot.seed q.1} :=
    surface_eq_graph cert.snapshot.rings (geometryView cert.snapshot.seed) seedChecked
  have graphOutput:=surface_eq_graph cert.snapshot.rings cert.snapshot.output outputChecked
  refine ⟨bindings,check_sound (seedCertificate request) (seedCertificate cert) seedAccepted,?_,domainEq,
    (fun i hi j hj => mesh_intersection_sound cert.snapshot.rings cert.snapshot.output outputChecked i j hi hj),
    ⟨graphHomeomorph cert.snapshot.rings (geometryView cert.snapshot.seed) seedChecked⟩,⟨graphHomeomorph cert.snapshot.rings cert.snapshot.output outputChecked⟩,bound,?_,?_,?_,?_,?_,?_⟩
  · rw [bindings.2.2.1,bindings.2.2.2.1]
    exact seedCoverage.trans domainEq
  · intro zero p hp
    have h:=bound p hp
    rw [zero,Rat.cast_zero] at h
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
  · intro original member required
    have chain:=check2_preserved_chain request cert accepted original member required
    refine ⟨chainFrom_sound cert.snapshot.seed cert.snapshot.output original
      (ownerSegments cert.snapshot.output original.owner) original.a 0 chain,?_⟩
    have covered:=chainFrom_parameter_cover cert.snapshot.seed cert.snapshot.output original
      (ownerSegments cert.snapshot.output original.owner) original.a 0 chain
    simpa only [Rat.cast_zero] using covered

  · intro q hq
    rw [graphSeed] at hq
    refine ⟨(q.1,globalHeight cert.snapshot.output q.1),?_,rfl,?_⟩
    · rw [graphOutput]
      exact ⟨domainEq ▸ hq.1,rfl⟩
    · have h:=bound q.1 (domainEq ▸ hq.1)
      simpa [euclideanDistance,hq.2,Real.sqrt_sq_eq_abs] using h
  · intro q hq
    rw [graphOutput] at hq
    refine ⟨(q.1,globalHeight cert.snapshot.seed q.1),?_,rfl,?_⟩
    · rw [graphSeed]
      exact ⟨domainEq.symm ▸ hq.1,rfl⟩
    · have h:=bound q.1 hq.1
      simpa [euclideanDistance,hq.2,Real.sqrt_sq_eq_abs,abs_sub_comm] using h
  · apply stableInputCheck_sound
    have h:=accepted
    simp only [check2,Bool.and_eq_true] at h
    exact h.1.1.1.1.1.2
  · exact check2_fixed_constraint request cert accepted

#print axioms check2_sound
end Tess
