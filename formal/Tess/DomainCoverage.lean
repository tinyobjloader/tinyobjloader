import Tess.Coverage
import Tess.Generic
noncomputable section
namespace Tess.RealGeometry
open Set

def openRegion (points : Nat → P2) (faces : List Tess.Face) : Set P2 :=
  faces.foldr (fun f s => openTriangle (points f.a) (points f.b) (points f.c) ∪ s) ∅
def closedRegion (points : Nat → P2) (faces : List Tess.Face) : Set P2 :=
  faces.foldr (fun f s => closedTriangle (points f.a) (points f.b) (points f.c) ∪ s) ∅
def windingDomain (points : Nat → P2) (boundary : List (Nat × Nat)) : Set P2 :=
  closure (interior {p | 0 < (boundary.map (fun (a,b) => edgeRay (points a) (points b) p)).sum})

theorem mem_openRegion (points : Nat → P2) (faces : List Tess.Face) (p : P2) :
    p ∈ openRegion points faces ↔ ∃ f ∈ faces, p ∈ openTriangle (points f.a) (points f.b) (points f.c) := by
  induction faces with
  | nil => simp [openRegion]
  | cons f tail ih =>
    simpa [openRegion] using (or_congr (Iff.rfl : (p ∈ openTriangle (points f.a) (points f.b) (points f.c)) ↔ _) ih)

theorem openRegion_open (points : Nat → P2) (faces : List Tess.Face) : IsOpen (openRegion points faces) := by
  induction faces with
  | nil => exact isOpen_empty
  | cons f tail ih => exact (isOpen_openTriangle _ _ _).union ih

theorem closure_openRegion (points : Nat → P2) (faces : List Tess.Face)
    (positive : ∀ f ∈ faces, 0<orient (points f.a) (points f.b) (points f.c)) :
    closure (openRegion points faces) = closedRegion points faces := by
  induction faces with
  | nil => simp [openRegion,closedRegion]
  | cons f tail ih =>
    change closure (openTriangle (points f.a) (points f.b) (points f.c) ∪ openRegion points tail) =
      closedTriangle (points f.a) (points f.b) (points f.c) ∪ closedRegion points tail
    rw [closure_union,triangle_closure _ _ _ (positive f (by simp)),ih (fun g hg => positive g (by simp [hg]))]

private theorem indicator_sum (faces : List Tess.Face) (predicate : Tess.Face → Prop) [DecidablePred predicate] :
    0 ≤ (faces.map (fun f => if predicate f then (1 : ℤ) else 0)).sum ∧
    (0 < (faces.map (fun f => if predicate f then (1 : ℤ) else 0)).sum ↔ ∃ f ∈ faces, predicate f) := by
  classical
  induction faces with
  | nil => simp
  | cons f tail ih =>
    by_cases hf : predicate f
    · simp only [List.map_cons,if_pos hf,List.sum_cons,List.mem_cons]
      constructor
      · omega
      · constructor
        · intro _; exact ⟨f,Or.inl rfl,hf⟩
        · intro _; omega
    · simpa [hf] using ih

private theorem edge_triangle_sum (points : Nat → P2) (faces : List Tess.Face) (p : P2) :
    ((faces.flatMap Tess.Face.edges).map (fun (a,b) => edgeRay (points a) (points b) p)).sum =
    (faces.map (fun f => triangleWinding (points f.a) (points f.b) (points f.c) p)).sum := by
  induction faces with
  | nil => simp
  | cons f tail ih => simp [Tess.Face.edges,triangleWinding,List.sum_append,ih,add_assoc]

/-- Positive faces and equality of normalized boundary chains imply coverage
of the prescribed winding domain. Coverage is the conclusion, not a premise.
The finite-arrangement/closure argument includes all edges and vertices. -/
theorem planar_coverage (points : Nat → P2) (faces : List Tess.Face) (boundary : List (Nat × Nat))
    (positive : ∀ f ∈ faces, 0<orient (points f.a) (points f.b) (points f.c))
    (chains : ∀ a b, Tess.balance (faces.flatMap Tess.Face.edges) a b = Tess.balance boundary a b) :
    windingDomain points boundary = closedRegion points faces := by
  classical
  let generic := genericSet (arrangement points faces)
  have agree : {p | 0 < (boundary.map (fun (a,b) => edgeRay (points a) (points b) p)).sum} ∩ generic =
      openRegion points faces ∩ generic := by
    ext p
    by_cases hg : p ∈ generic
    · have hmap : (faces.map (fun f => triangleWinding (points f.a) (points f.b) (points f.c) p)) =
          faces.map (fun f => if p ∈ openTriangle (points f.a) (points f.b) (points f.c) then (1 : ℤ) else 0) := by
        apply List.map_congr_left
        intro f hf
        have hgeneric := generic_face points faces f hf p hg
        simpa only [openTriangle,Set.mem_setOf_eq] using triangle_winding_indicator _ _ _ _ (positive f hf)
          hgeneric.1 hgeneric.2.1 hgeneric.2.2.1 hgeneric.2.2.2.1 hgeneric.2.2.2.2.1 hgeneric.2.2.2.2.2
      have equal := boundary_winding_eq (faces.flatMap Tess.Face.edges) boundary chains points p
      rw [edge_triangle_sum,hmap] at equal
      have indicator := (indicator_sum faces (fun f => p ∈ openTriangle (points f.a) (points f.b) (points f.c))).2
      simp only [mem_inter_iff,mem_setOf_eq,hg,and_true]
      rw [← equal,indicator,mem_openRegion]
    · simp [hg]
  rw [windingDomain,regularized_eq_of_generic _ _ _ (openRegion_open points faces)
    (generic_open _) (arrangement_dense points faces positive) agree,closure_openRegion points faces positive]

#print axioms planar_coverage
end Tess.RealGeometry
