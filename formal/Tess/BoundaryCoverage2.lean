import Tess.ChainSoundness
import Tess.V2
noncomputable section
namespace Tess
open RealGeometry Set

/-- Removing a closed nowhere-dense arrangement cannot affect regularized
interiors. This handles boundary and horizontal-line points by closure. -/
theorem regularized_inter_dense_open (A G : Set P2) (openG : IsOpen G) (denseG : Dense G) :
    closure (interior (A∩G))=closure (interior A) := by
  rw [interior_inter,openG.interior_eq]
  apply Set.Subset.antisymm
  · exact closure_mono inter_subset_left
  · exact closure_minimal (denseG.open_subset_closure_inter isOpen_interior) isClosed_closure

def constraintLines (m : ExactMesh) : List Line :=
  m.constraints.toList.flatMap fun e => [horizontal (realPoint m e.a),horizontal (realPoint m e.b)]

theorem constraintLines_nonconstant (m : ExactMesh) : ∀ l∈constraintLines m,nonconstant l := by
  intro l hl
  obtain ⟨e,he,hl⟩:=List.mem_flatMap.mp hl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl <;> simp [horizontal,nonconstant]

theorem constraintLines_generic (m : ExactMesh) (p : P2) (generic : p∈genericSet (constraintLines m)) :
    ∀ e∈m.constraints, (realPoint m e.a).2≠p.2 ∧ (realPoint m e.b).2≠p.2 := by
  intro e he
  have ga:=generic (horizontal (realPoint m e.a))
    (List.mem_flatMap.mpr ⟨e,by simpa using he,by simp⟩)
  have gb:=generic (horizontal (realPoint m e.b))
    (List.mem_flatMap.mpr ⟨e,by simpa using he,by simp⟩)
  simp only [lineValue,horizontal,affineValue,zero_mul,one_mul,zero_add,← sub_eq_add_neg] at ga gb
  exact ⟨Ne.symm (sub_ne_zero.mp ga),Ne.symm (sub_ne_zero.mp gb)⟩

theorem check2_seed_checked (request cert : Certificate2) (accepted : check2 request cert=true) :
    check (seedCertificate request) (seedCertificate cert)=true := by
  simp only [check2,Bool.and_eq_true] at accepted
  exact accepted.1.1.1.1.1.1.1.2

theorem check2_domains (request cert : Certificate2) (accepted : check2 request cert=true) :
    meshDomain cert.snapshot.seed=meshDomain cert.snapshot.output := by
  have seedChecked:=check2_seed_checked request cert accepted
  have seedCoverage : windingDomain (realPoint cert.snapshot.seed) (ringEdges cert.snapshot.rings)=
      meshDomain cert.snapshot.seed := check_seed_coverage (seedCertificate request) (seedCertificate cert) seedChecked
  have outChecked:=check2_output_checked request cert accepted
  have outputCoverage : windingDomain (realPoint cert.snapshot.output) (expandedBoundary cert)=
      meshDomain cert.snapshot.output := by
    apply planar_coverage
    · intro f hf
      exact meshPositive _ _ outChecked f (by simpa using hf)
    · have boundary : boundaryCheckEdges (expandedBoundary cert) cert.snapshot.output=true := by
        simp only [meshCheck,Bool.and_eq_true] at outChecked; exact outChecked.1.2
      exact boundary_all_coefficients_edges _ _ boundary
  let G:=genericSet (constraintLines cert.snapshot.seed) ∩ genericSet (constraintLines cert.snapshot.output)
  have openG : IsOpen G:=(generic_open _).inter (generic_open _)
  have denseG : Dense G:=(generic_dense _ (constraintLines_nonconstant _)).inter_of_isOpen_left
    (generic_dense _ (constraintLines_nonconstant _)) (generic_open _)
  have agree : {p | 0<((expandedBoundary cert).map (fun (a,b) => edgeRay (realPoint cert.snapshot.output a)
      (realPoint cert.snapshot.output b) p)).sum} ∩ G =
      {p | 0<((ringEdges cert.snapshot.rings).map (fun (a,b) => edgeRay (realPoint cert.snapshot.seed a)
        (realPoint cert.snapshot.seed b) p)).sum} ∩ G := by
    ext p
    by_cases hg:p∈G
    · simp only [mem_inter_iff,mem_setOf_eq,hg,and_true]
      rw [check2_boundary_winding request cert accepted p
        (constraintLines_generic _ p hg.1) (constraintLines_generic _ p hg.2)]
    · simp [hg]
  have windingEq : windingDomain (realPoint cert.snapshot.output) (expandedBoundary cert)=
      windingDomain (realPoint cert.snapshot.seed) (ringEdges cert.snapshot.rings) := by
    unfold windingDomain
    have left:=regularized_inter_dense_open
      {p | 0<((expandedBoundary cert).map (fun (a,b) => edgeRay (realPoint cert.snapshot.output a)
        (realPoint cert.snapshot.output b) p)).sum} G openG denseG
    have right:=regularized_inter_dense_open
      {p | 0<((ringEdges cert.snapshot.rings).map (fun (a,b) => edgeRay (realPoint cert.snapshot.seed a)
        (realPoint cert.snapshot.seed b) p)).sum} G openG denseG
    exact left.symm.trans ((congrArg (fun A : Set P2 => closure (interior A)) agree).trans right)
  exact seedCoverage.symm.trans (windingEq.symm.trans outputCoverage)

#print axioms check2_domains
end Tess
