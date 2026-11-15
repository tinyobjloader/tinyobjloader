import Tess.Graph
noncomputable section
namespace Tess
open RealGeometry Set

theorem seed_output_domain (request cert : Certificate) (h : check request cert=true) :
    meshDomain cert.seed=meshDomain cert.output := by
  have valid := check_structural_sound request cert h
  have hd : domainCheck cert.rings cert.seed=true := by
    simp only [check,Bool.and_eq_true] at h; aesop
  have bounds : allN cert.rings.size (fun r => decide (cert.rings[r]?.getD 0 ≤ cert.seed.points.size))=true := by
    simp only [domainCheck,Bool.and_eq_true] at hd; aesop
  simp only [allN,List.all_eq_true,List.mem_range,decide_eq_true_eq] at bounds
  have transform : cert.seed.u=cert.output.u ∧ cert.seed.w=cert.output.w := by
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h; aesop
  have fixed (i : Nat) (hi : i<cert.seed.points.size) : realPoint cert.seed i=realPoint cert.output i := by
    simp only [realPoint,ExactMesh.project,valid.fixedInput i hi,transform.1,transform.2]
  have boundaryEqual := windingDomain_congr_on_edges (ringEdges cert.rings) (realPoint cert.seed) (realPoint cert.output)
    (fun e he => ⟨fixed e.1 (ringEdges_bounds _ _ bounds e he).1,fixed e.2 (ringEdges_bounds _ _ bounds e he).2⟩)
  exact (check_seed_coverage request cert h).symm.trans (boundaryEqual.trans (check_output_coverage request cert h))

theorem heightPlane_real (m : ExactMesh) (f : Face) (p : P2) :
    affineValue ((heightPlane m f).x : ℝ) ((heightPlane m f).y : ℝ) ((heightPlane m f).c : ℝ) p = faceHeight m f p := by
  simp only [faceHeight,affineLift_coefficients,heightPlane,Separator.scale,Separator.add,supportingLine,
    liftCoefficients,affineValue,realPoint,Tess.orient,RealGeometry.orient]
  push_cast
  ring

theorem equalPlanes_heights (seed output : ExactMesh) (a b : Face)
    (h : planesEqual (heightPlane seed a) (heightPlane output b)=true) :
    ∀ p, faceHeight seed a p=faceHeight output b p := by
  simp only [planesEqual,decide_eq_true_eq] at h
  intro p
  rw [← heightPlane_real,← heightPlane_real,h.1,h.2.1,h.2.2]

private theorem cross_orient_cast (a b : ExactMesh) (x y z : Nat) :
    RealGeometry.orient (realPoint a x) (realPoint a y) (realPoint b z) =
      ((Tess.orient (a.project x) (a.project y) (b.project z)) : ℝ) := by
  simp [RealGeometry.orient,Tess.orient,realPoint]

/-- A checked supporting-edge separator excludes a common interior point. -/
theorem edgeSeparates_sound (a : ExactMesh) (fa : Face) (b : ExactMesh) (fb : Face)
    (positive : 0<RealGeometry.orient (realPoint b fb.a) (realPoint b fb.b) (realPoint b fb.c))
    (h : edgeSeparates a fa b fb=true) (p : P2)
    (ha : p∈openTriangle (realPoint a fa.a) (realPoint a fa.b) (realPoint a fa.c))
    (hb : p∈faceRegion b fb) : False := by
  simp only [edgeSeparates,List.any_eq_true] at h
  obtain ⟨edge,he,hv⟩ := h
  have edgePositive : 0<RealGeometry.orient (realPoint a edge.1) (realPoint a edge.2) p := by
    simp [Face.edges] at he
    rcases he with rfl|rfl|rfl
    · exact ha.1
    · exact ha.2.1
    · exact ha.2.2
  have values : ∀ i∈fb.ids, RealGeometry.orient (realPoint a edge.1) (realPoint a edge.2) (realPoint b i)≤0 := by
    intro i hi
    have hv := (List.all_eq_true.mp hv) i hi
    rw [cross_orient_cast]
    exact_mod_cast of_decide_eq_true hv
  obtain ⟨u,v,w,hu,hv,hw,total,repr⟩ := (barycentric _ _ _ _ positive).mp hb
  have hpNonpositive : RealGeometry.orient (realPoint a edge.1) (realPoint a edge.2) p≤0 := by
    rw [← repr,orient_combo3 _ _ _ _ _ _ _ _ total]
    exact add_nonpos (add_nonpos (mul_nonpos_of_nonneg_of_nonpos hu (values fb.a (by simp [Face.ids])))
      (mul_nonpos_of_nonneg_of_nonpos hv (values fb.b (by simp [Face.ids]))))
      (mul_nonpos_of_nonneg_of_nonpos hw (values fb.c (by simp [Face.ids])))
  exact not_lt_of_ge hpNonpositive edgePositive

/-- Exact preservation on every real chart coordinate, not only mesh vertices.
The extra plane/separator gate makes the zero-tolerance proof independent of
an unproved overlay-enumeration completeness assumption. -/
theorem check_exact_reference (request cert : Certificate) (accepted : check request cert=true) :
    EqOn (globalHeight cert.seed) (globalHeight cert.output) (meshDomain cert.output) := by
  have seedChecked : meshCheck cert.rings cert.seed=true := by
    simp only [check,Bool.and_eq_true] at accepted; aesop
  have outputChecked : meshCheck cert.rings cert.output=true := by
    simp only [check,Bool.and_eq_true] at accepted; aesop
  have reference : referenceCheck cert.seed cert.output=true := by
    simp only [check,Bool.and_eq_true] at accepted; aesop
  have planes : planeReferenceCheck cert.seed cert.output=true := by
    simp only [referenceCheck,Bool.and_eq_true] at reference; exact reference.2
  have seedPositive := meshPositive cert.rings cert.seed seedChecked
  have outputPositive := meshPositive cert.rings cert.output outputChecked
  have seedPositiveList : ∀ f∈cert.seed.faces.toList, 0<RealGeometry.orient (realPoint cert.seed f.a)
      (realPoint cert.seed f.b) (realPoint cert.seed f.c) := fun f hf => seedPositive f (by simpa using hf)
  have outputPositiveList : ∀ f∈cert.output.faces.toList, 0<RealGeometry.orient (realPoint cert.output f.a)
      (realPoint cert.output f.b) (realPoint cert.output f.c) := fun f hf => outputPositive f (by simpa using hf)
  let G := genericSet (arrangement (realPoint cert.seed) cert.seed.faces.toList) ∩
    genericSet (arrangement (realPoint cert.output) cert.output.faces.toList)
  have denseG : Dense G := (arrangement_dense _ _ seedPositiveList).inter_of_isOpen_left
    (arrangement_dense _ _ outputPositiveList) (generic_open _)
  let U := openRegion (realPoint cert.output) cert.output.faces.toList
  have subsetDomain : U ∩ G ⊆ meshDomain cert.output := by
    intro p hp
    obtain ⟨b,hb,hp⟩ := (mem_openRegion _ _ p).mp hp.1
    apply (mem_closedRegion cert.output cert.output.faces.toList p).mpr
    exact ⟨b,hb,hp.1.le,hp.2.1.le,hp.2.2.le⟩
  have equalOn : EqOn (globalHeight cert.seed) (globalHeight cert.output) (U ∩ G) := by
    intro p hp
    obtain ⟨b,hb,pb⟩ := (mem_openRegion _ _ p).mp hp.1
    have hbArray : b∈cert.output.faces := by simpa using hb
    have outputMember := subsetDomain hp
    have seedMember : p∈meshDomain cert.seed := by
      rw [seed_output_domain request cert accepted]; exact outputMember
    obtain ⟨a,ha,pa⟩ := (mem_closedRegion cert.seed cert.seed.faces.toList p).mp seedMember
    have haArray : a∈cert.seed.faces := by simpa using ha
    have genericSeed := generic_face (realPoint cert.seed) cert.seed.faces.toList a ha p hp.2.1
    have paOpen : p∈openTriangle (realPoint cert.seed a.a) (realPoint cert.seed a.b) (realPoint cert.seed a.c) :=
      ⟨lt_of_le_of_ne pa.1 (Ne.symm genericSeed.2.2.2.1),
       lt_of_le_of_ne pa.2.1 (Ne.symm genericSeed.2.2.2.2.1),
       lt_of_le_of_ne pa.2.2 (Ne.symm genericSeed.2.2.2.2.2)⟩
    have pair := (Array.all_eq_true'.mp ((Array.all_eq_true'.mp planes) a haArray)) b hbArray
    simp only [Bool.or_eq_true] at pair
    have heightEq : faceHeight cert.seed a p=faceHeight cert.output b p := by
      rcases pair with same|separated
      · exact equalPlanes_heights _ _ _ _ same p
      · simp only [noInteriorOverlap,Bool.or_eq_true] at separated
        rcases separated with left|right
        · exact (edgeSeparates_sound _ _ _ _ (outputPositive b hbArray) left p paOpen
            ⟨pb.1.le,pb.2.1.le,pb.2.2.le⟩).elim
        · exact (edgeSeparates_sound _ _ _ _ (seedPositive a haArray) right p pb pa).elim
    rw [globalHeight_on_face cert.rings cert.seed seedChecked a haArray p pa,
        globalHeight_on_face cert.rings cert.output outputChecked b hbArray p ⟨pb.1.le,pb.2.1.le,pb.2.2.le⟩]
    exact heightEq
  have closureSubset : meshDomain cert.output ⊆ closure (U ∩ G) := by
    have hu : U ⊆ closure (U ∩ G) := denseG.open_subset_closure_inter (openRegion_open _ _)
    have hh := closure_minimal hu isClosed_closure
    simpa only [U,closure_openRegion _ _ outputPositiveList,meshDomain] using hh
  apply equalOn.of_subset_closure _ (globalHeight_continuousOn cert.rings cert.output outputChecked) subsetDomain closureSubset
  rw [← seed_output_domain request cert accepted]
  exact globalHeight_continuousOn cert.rings cert.seed seedChecked

#print axioms check_exact_reference
end Tess
