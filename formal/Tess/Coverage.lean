import Tess.Soundness
import Tess.Winding
import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Tess
private theorem balance_swap (edges : List (Nat × Nat)) (a b : Nat) :
    balance edges b a = -balance edges a b := by unfold balance; ring

/-- The executable finite support check implies equality of every coefficient,
including reversed edges and pairs absent from both lists. -/
theorem boundary_all_coefficients_edges (expected : List (Nat × Nat)) (m : ExactMesh)
    (h : boundaryCheckEdges expected m = true) (a b : Nat) :
    balance (faceEdges m) a b = balance (expected) a b := by
  simp only [boundaryCheckEdges, List.all_eq_true, decide_eq_true_eq] at h
  by_cases hab : (a,b) ∈ faceEdges m ++ expected
  · exact h (a,b) hab
  by_cases hba : (b,a) ∈ faceEdges m ++ expected
  · have hv := h (b,a) hba
    rw [balance_swap (faceEdges m) a b, balance_swap (expected) a b] at hv
    omega
  have ha : (a,b) ∉ faceEdges m := fun hp => hab (List.mem_append_left _ hp)
  have hb : (a,b) ∉ expected := fun hp => hab (List.mem_append_right _ hp)
  have hc : (b,a) ∉ faceEdges m := fun hp => hba (List.mem_append_left _ hp)
  have hd : (b,a) ∉ expected := fun hp => hba (List.mem_append_right _ hp)
  simp [balance, List.count_eq_zero.mpr ha, List.count_eq_zero.mpr hb,
    List.count_eq_zero.mpr hc, List.count_eq_zero.mpr hd]

theorem boundary_all_coefficients (rings : Array Nat) (m : ExactMesh)
    (h : boundaryCheck rings m=true) (a b : Nat) :
    balance (faceEdges m) a b=balance (orientedBoundary rings m) a b :=
  boundary_all_coefficients_edges (ringEdges rings) m h a b

private theorem swap_count (edges : List (Nat × Nat)) (a b : Nat) :
    (edges.map Prod.swap).count (a,b) = edges.count (b,a) := by
  simpa using List.count_map_of_injective edges Prod.swap Prod.swap_injective (b,a)

/-- Cancellation works for any antisymmetric edge functional, independently of
geometry. Winding is the application used below. -/
theorem chain_functional_eq (actual expected : List (Nat × Nat))
    (coefficients : ∀ a b, balance actual a b = balance expected a b)
    (weight : Nat × Nat → ℤ) (anti : ∀ a b, weight (b,a) = -weight (a,b)) :
    (actual.map weight).sum = (expected.map weight).sum := by
  have perm : (actual ++ expected.map Prod.swap).Perm (expected ++ actual.map Prod.swap) := by
    apply List.perm_iff_count.mpr
    rintro ⟨a,b⟩
    simp only [List.count_append, swap_count]
    have h := coefficients a b
    unfold balance at h
    omega
  have summed := (perm.map weight).sum_eq
  have hm (edges : List (Nat × Nat)) :
      ((edges.map Prod.swap).map weight).sum = -(edges.map weight).sum := by
    simp only [List.map_map, Function.comp_def]
    simp only [show (fun e : Nat × Nat => weight e.swap) = (fun e => -weight e) from
      funext (fun ⟨a,b⟩ => anti a b)]
    simpa only [List.map_map, Function.comp_def] using (List.sum_neg (edges.map weight)).symm
  simp only [List.map_append, List.sum_append, hm] at summed
  omega
end Tess

namespace Tess.RealGeometry

theorem edgeRay_reverse (a b p : P2) : edgeRay b a p = -edgeRay a b p := by
  have swap : orient b a p = -orient a b p := by simp only [orient]; ring
  simp only [edgeRay, swap, rayDelta, neg_pos, neg_lt_zero]
  split_ifs <;> simp_all <;> linarith

/-- Equal normalized boundary chains have equal ray-crossing winding. The
coordinates may be arbitrary reals: rational-to-real transport is separate. -/
theorem boundary_winding_eq (actual expected : List (Nat × Nat))
    (coefficients : ∀ a b, Tess.balance actual a b = Tess.balance expected a b)
    (points : Nat → P2) (p : P2) :
    (actual.map (fun (a,b) => edgeRay (points a) (points b) p)).sum =
    (expected.map (fun (a,b) => edgeRay (points a) (points b) p)).sum := by
  exact Tess.chain_functional_eq actual expected coefficients _
    (fun a b => edgeRay_reverse (points a) (points b) p)
#print axioms boundary_winding_eq
end Tess.RealGeometry
