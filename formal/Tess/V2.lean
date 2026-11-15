import Tess.V2Check
import Tess.Validity
namespace Tess
theorem check2_output_checked (request cert : Certificate2) (h : check2 request cert=true) :
    meshCheck cert.snapshot.rings cert.snapshot.output (expandedBoundary cert)=true := by
  simp only [check2,Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem check2_output_graph (request cert : Certificate2) (h : check2 request cert=true) :
    Nonempty ({p // p∈meshDomain cert.snapshot.output} ≃ₜ {q // q∈surface cert.snapshot.output}) :=
  ⟨graphHomeomorph _ _ (check2_output_checked request cert h)⟩

#print axioms check2_output_graph
end Tess
