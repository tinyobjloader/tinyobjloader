import Tess.ChainSoundness
noncomputable section
namespace Tess
open Set

/-- Include the terminal endpoint, even for a zero-length tail of a chain. -/
def parameterCover (segments : List Constraint) : Set ℝ :=
  segments.foldr (fun e tail => Icc (e.ta : ℝ) (e.tb : ℝ) ∪ tail) {1}

theorem chainFrom_parameter_cover (seed output : ExactMesh) (original : Constraint)
    (segments : List Constraint) (v : Nat) (t : Rat)
    (checked : chainFrom seed output original v t segments=true) :
    parameterCover segments=Icc (t : ℝ) 1 := by
  induction segments generalizing v t with
  | nil =>
    simp only [chainFrom,decide_eq_true_eq] at checked
    simp [parameterCover,checked.2]
  | cons e tail ih =>
    simp only [chainFrom,Bool.and_eq_true,decide_eq_true_eq] at checked
    rcases checked.1 with ⟨av,tv,order,upper,rest⟩
    simp only [parameterCover,List.foldr_cons]
    change Icc (e.ta : ℝ) (e.tb : ℝ) ∪ parameterCover tail=Icc (t : ℝ) 1
    rw [ih e.b e.tb checked.2,tv]
    exact Icc_union_Icc_eq_Icc (by exact_mod_cast (show t≤e.tb by rw [← tv]; exact order.le)) (by exact_mod_cast upper)

/-- Every segment carries the original kind, source, owner, tag and exact 3D
point on the original affine edge. Strict ordering and matching endpoints are
checked recursively, rather than inferred from an unordered segment set. -/
def OrderedConstraintChain (seed output : ExactMesh) (original : Constraint) :
    Nat → Rat → List Constraint → Prop
  | v,t,[] => v=original.b ∧ t=1
  | v,t,e::tail => e.a=v ∧ e.ta=t ∧ e.ta<e.tb ∧ e.tb≤1 ∧
      e.kind=original.kind ∧ e.source=original.source ∧ e.owner=original.owner ∧ e.tag=original.tag ∧
      e.a<output.points.size ∧ e.b<output.points.size ∧ e.a≠e.b ∧
      output.point e.a=pointAt (seed.point original.a) (seed.point original.b) e.ta ∧
      output.point e.b=pointAt (seed.point original.a) (seed.point original.b) e.tb ∧
      OrderedConstraintChain seed output original e.b e.tb tail

theorem chainFrom_sound (seed output : ExactMesh) (original : Constraint)
    (segments : List Constraint) (v : Nat) (t : Rat)
    (checked : chainFrom seed output original v t segments=true) :
    OrderedConstraintChain seed output original v t segments := by
  induction segments generalizing v t with
  | nil => simpa [chainFrom,OrderedConstraintChain] using checked
  | cons e tail ih =>
    simp only [chainFrom,Bool.and_eq_true,decide_eq_true_eq] at checked
    exact ⟨checked.1.1,checked.1.2.1,checked.1.2.2.1,checked.1.2.2.2.1,
      checked.1.2.2.2.2.1,checked.1.2.2.2.2.2.1,checked.1.2.2.2.2.2.2.1,
      checked.1.2.2.2.2.2.2.2.1,checked.1.2.2.2.2.2.2.2.2.1,
      checked.1.2.2.2.2.2.2.2.2.2.1,checked.1.2.2.2.2.2.2.2.2.2.2.1,
      checked.1.2.2.2.2.2.2.2.2.2.2.2.1,checked.1.2.2.2.2.2.2.2.2.2.2.2.2,
      ih e.b e.tb checked.2⟩

/-- Only implicit creases may disappear, and only for a positive tolerance. -/
theorem check2_preserved_chain (request cert : Certificate2) (accepted : check2 request cert=true)
    (original : Constraint) (member : original∈cert.snapshot.seed.constraints)
    (required : original.kind≠2 ∨ cert.run.tolerance=0) :
    chainFrom cert.snapshot.seed cert.snapshot.output original original.a 0
      (ownerSegments cert.snapshot.output original.owner)=true := by
  have hc : extendedConstraints cert=true := by
    simp only [check2,Bool.and_eq_true] at accepted; aesop
  simp only [extendedConstraints,Bool.and_eq_true] at hc
  have item:=Array.all_eq_true'.mp hc.1.1.2 original member
  simp only [Bool.and_eq_true] at item
  have chain:=item.2
  have noDrop : ¬((original.kind=2 ∧ 0<cert.run.tolerance) ∧
      (ownerSegments cert.snapshot.output original.owner).isEmpty=true) := by
    rcases required with different|zero
    · simp [different]
    · simp [zero]
  simp only [Bool.and_eq_true,decide_eq_true_eq] at chain
  rw [if_neg noDrop] at chain
  simp only [Bool.and_eq_true] at chain
  exact chain.1

theorem check2_fixed_constraint (request cert : Certificate2) (accepted : check2 request cert=true)
    (original : Constraint) (member : original∈cert.snapshot.seed.constraints)
    (required : original.kind≠2 ∨ cert.run.tolerance=0)
    (fixed : permittedSubdivision cert.run original=false) :
    (ownerSegments cert.snapshot.output original.owner).length=1 := by
  have hc : extendedConstraints cert=true := by
    simp only [check2,Bool.and_eq_true] at accepted; aesop
  simp only [extendedConstraints,Bool.and_eq_true] at hc
  have item:=Array.all_eq_true'.mp hc.1.1.2 original member
  simp only [Bool.and_eq_true] at item
  have chain:=item.2
  have noDrop : ¬((original.kind=2 ∧ 0<cert.run.tolerance) ∧
      (ownerSegments cert.snapshot.output original.owner).isEmpty=true) := by
    rcases required with different|zero
    · simp [different]
    · simp [zero]
  simp only [Bool.and_eq_true,decide_eq_true_eq] at chain
  rw [if_neg noDrop] at chain
  simp only [Bool.and_eq_true] at chain
  simpa only [fixed,Bool.false_or,decide_eq_true_eq] using chain.2

#print axioms chainFrom_parameter_cover
#print axioms chainFrom_sound
end Tess
