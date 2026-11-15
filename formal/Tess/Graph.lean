import Tess.Lift
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.ContinuousOn
noncomputable section
namespace Tess
open RealGeometry Set

def meshDomain (m : ExactMesh) : Set P2 := closedRegion (realPoint m) m.faces.toList
def surface (m : ExactMesh) : Set (P2 × ℝ) :=
  {q | ∃ f∈m.faces, q.1∈faceRegion m f ∧ q.2=faceHeight m f q.1}
def globalHeight (m : ExactMesh) (p : P2) : ℝ := by
  classical
  exact if h : ∃ f∈m.faces, p∈faceRegion m f then faceHeight m h.choose p else 0

theorem mem_closedRegion (m : ExactMesh) (faces : List Face) (p : P2) :
    p∈closedRegion (realPoint m) faces ↔ ∃ f∈faces, p∈faceRegion m f := by
  induction faces with
  | nil => simp [closedRegion]
  | cons f tail ih =>
    simpa [closedRegion,faceRegion] using
      (or_congr (Iff.rfl : p∈faceRegion m f ↔ _) ih)

theorem closedRegion_closed (m : ExactMesh) (faces : List Face) :
    IsClosed (closedRegion (realPoint m) faces) := by
  induction faces with
  | nil => exact isClosed_empty
  | cons f tail ih => exact (isClosed_closedTriangle _ _ _).union ih

theorem globalHeight_on_face (rings : Array Nat) (m : ExactMesh) {expected : List (Nat × Nat)} (checked : meshCheck rings m expected=true)
    (f : Face) (hf : f∈m.faces) (p : P2) (hp : p∈faceRegion m f) :
    globalHeight m p=faceHeight m f p := by
  have h : ∃ f∈m.faces, p∈faceRegion m f := ⟨f,hf,hp⟩
  rw [globalHeight,dif_pos h]
  exact mesh_height_agreement rings m checked h.choose h.choose_spec.1 f hf p ⟨h.choose_spec.2,hp⟩

/-- Finite closed-face gluing yields a continuous PL height over the entire
closed domain, including boundaries and creases. -/
theorem globalHeight_continuousOn (rings : Array Nat) (m : ExactMesh) {expected : List (Nat × Nat)} (checked : meshCheck rings m expected=true) :
    ContinuousOn (globalHeight m) (meshDomain m) := by
  have finiteGlue (faces : List Face) (subset : ∀ f∈faces, f∈m.faces) :
      ContinuousOn (globalHeight m) (closedRegion (realPoint m) faces) := by
    induction faces with
    | nil => exact continuousOn_empty _
    | cons f tail ih =>
      have hf := subset f (by simp)
      have faceContinuous : ContinuousOn (globalHeight m) (faceRegion m f) := by
        apply (continuous_affineLift _ _ _ _ _ _).continuousOn.congr
        intro p hp
        exact globalHeight_on_face rings m checked f hf p hp
      exact faceContinuous.union_of_isClosed (ih (fun g hg => subset g (by simp [hg])))
        (isClosed_closedTriangle _ _ _) (closedRegion_closed m tail)
  exact finiteGlue m.faces.toList (fun f hf => by simpa using hf)

theorem surface_eq_graph (rings : Array Nat) (m : ExactMesh) {expected : List (Nat × Nat)} (checked : meshCheck rings m expected=true) :
    surface m = {q : P2×ℝ | q.1∈meshDomain m ∧ q.2=globalHeight m q.1} := by
  ext q
  constructor
  · rintro ⟨f,hf,hp,height⟩
    refine ⟨(mem_closedRegion m m.faces.toList q.1).mpr ⟨f,by simpa using hf,hp⟩,?_⟩
    rw [globalHeight_on_face rings m checked f hf q.1 hp]
    exact height
  · rintro ⟨hp,height⟩
    obtain ⟨f,hf,hp⟩ := (mem_closedRegion m m.faces.toList q.1).mp hp
    refine ⟨f,by simpa using hf,hp,?_⟩
    rw [height]
    exact globalHeight_on_face rings m checked f (by simpa using hf) q.1 hp

/-- Projection and PL lifting are inverse continuous maps. Thus the supplied
surface is embedded and has exactly the topology of its admitted chart domain. -/
def graphHomeomorph (rings : Array Nat) (m : ExactMesh) {expected : List (Nat × Nat)} (checked : meshCheck rings m expected=true) :
    {p // p∈meshDomain m} ≃ₜ {q // q∈surface m} where
  toFun p := ⟨(p.val,globalHeight m p.val),by rw [surface_eq_graph rings m checked]; exact ⟨p.property,rfl⟩⟩
  invFun q := ⟨q.val.1,((Set.ext_iff.mp (surface_eq_graph rings m checked)) q.val |>.mp q.property).1⟩
  left_inv p := rfl
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h := ((Set.ext_iff.mp (surface_eq_graph rings m checked)) q.val).mp q.property
      exact h.2.symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.prodMk (continuousOn_iff_continuous_domRestrict.mp (globalHeight_continuousOn rings m checked))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.comp continuous_subtype_val
#print axioms graphHomeomorph
end Tess
