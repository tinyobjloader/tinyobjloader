import Tess.AffineBoundSoundness
import Mathlib.Topology.Order.OrderClosed
noncomputable section
namespace Tess
open RealGeometry Set

/-- Affine dual witnesses certify bounds on every overlap cell. Density and
continuity extend the result to all closed faces, creases and domain boundary. -/
theorem referenceBound_sound (rings : Array Nat) (seed output : ExactMesh)
    {seedBoundary outputBoundary : List (Nat × Nat)} (tolerance : Rat)
    (seedChecked : meshCheck rings seed seedBoundary=true)
    (outputChecked : meshCheck rings output outputBoundary=true)
    (domainEq : meshDomain seed=meshDomain output)
    (checked : referenceBoundCheck seed output tolerance=true) :
    ∀ p∈meshDomain output, |globalHeight seed p-globalHeight output p|≤(tolerance : ℝ) := by
  have nonnegative : 0≤tolerance := by
    simp only [referenceBoundCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    exact checked.1.1
  have planes : seed.faces.all (fun a => output.faces.all fun b => overlayPairBound seed a output b tolerance)=true := by
    simp only [referenceBoundCheck,Bool.and_eq_true] at checked
    exact checked.2
  have seedPositive := meshPositive rings seed seedChecked
  have outputPositive := meshPositive rings output outputChecked
  have seedPositiveList : ∀ f∈seed.faces.toList, 0<RealGeometry.orient (realPoint seed f.a)
      (realPoint seed f.b) (realPoint seed f.c) := fun f hf => seedPositive f (by simpa using hf)
  have outputPositiveList : ∀ f∈output.faces.toList, 0<RealGeometry.orient (realPoint output f.a)
      (realPoint output f.b) (realPoint output f.c) := fun f hf => outputPositive f (by simpa using hf)
  let G := genericSet (arrangement (realPoint seed) seed.faces.toList) ∩
    genericSet (arrangement (realPoint output) output.faces.toList)
  have denseG : Dense G := (arrangement_dense _ _ seedPositiveList).inter_of_isOpen_left
    (arrangement_dense _ _ outputPositiveList) (generic_open _)
  let U := openRegion (realPoint output) output.faces.toList
  have subsetDomain : U ∩ G ⊆ meshDomain output := by
    intro p hp
    obtain ⟨b,hb,hp⟩ := (mem_openRegion _ _ p).mp hp.1
    apply (mem_closedRegion output output.faces.toList p).mpr
    exact ⟨b,hb,hp.1.le,hp.2.1.le,hp.2.2.le⟩
  have equalOn : EqOn (fun p => max |globalHeight seed p-globalHeight output p| (tolerance : ℝ))
      (fun _ => (tolerance : ℝ)) (U ∩ G) := by
    intro p hp
    obtain ⟨b,hb,pb⟩ := (mem_openRegion _ _ p).mp hp.1
    have hbArray : b∈output.faces := by simpa using hb
    have outputMember := subsetDomain hp
    have seedMember : p∈meshDomain seed := by
      rw [domainEq]; exact outputMember
    obtain ⟨a,ha,pa⟩ := (mem_closedRegion seed seed.faces.toList p).mp seedMember
    have haArray : a∈seed.faces := by simpa using ha
    have genericSeed := generic_face (realPoint seed) seed.faces.toList a ha p hp.2.1
    have paOpen : p∈openTriangle (realPoint seed a.a) (realPoint seed a.b) (realPoint seed a.c) :=
      ⟨lt_of_le_of_ne pa.1 (Ne.symm genericSeed.2.2.2.1),
       lt_of_le_of_ne pa.2.1 (Ne.symm genericSeed.2.2.2.2.1),
       lt_of_le_of_ne pa.2.2 (Ne.symm genericSeed.2.2.2.2.2)⟩
    have pair := (Array.all_eq_true'.mp ((Array.all_eq_true'.mp planes) a haArray)) b hbArray
    have heightBound := overlayPairBound_sound seed output a b tolerance
      (seedPositive a haArray) (outputPositive b hbArray) pair nonnegative p paOpen pb
    dsimp only
    rw [globalHeight_on_face rings seed seedChecked a haArray p pa,
        globalHeight_on_face rings output outputChecked b hbArray p ⟨pb.1.le,pb.2.1.le,pb.2.2.le⟩]
    exact max_eq_right heightBound
  have closureSubset : meshDomain output ⊆ closure (U ∩ G) := by
    have hu : U ⊆ closure (U ∩ G) := denseG.open_subset_closure_inter (openRegion_open _ _)
    have hh := closure_minimal hu isClosed_closure
    simpa only [U,closure_openRegion _ _ outputPositiveList,meshDomain] using hh
  have seedContinuous : ContinuousOn (globalHeight seed) (meshDomain output) := by
    rw [← domainEq]
    exact globalHeight_continuousOn rings seed seedChecked
  have boundedContinuous : ContinuousOn (fun p => max |globalHeight seed p-globalHeight output p| (tolerance : ℝ))
      (meshDomain output) := continuous_max.comp_continuousOn
        ((seedContinuous.sub (globalHeight_continuousOn rings output outputChecked)).abs.prodMk continuousOn_const)
  have everywhere := equalOn.of_subset_closure boundedContinuous continuousOn_const subsetDomain closureSubset
  intro p hp
  have bound:=everywhere hp
  exact (max_eq_right_iff.mp bound)

#print axioms referenceBound_sound
end Tess
