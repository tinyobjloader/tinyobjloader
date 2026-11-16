/-
  The `qsort` comparator `cmp` of `tess_topology` (`lib/tess/src/topology.c`) on incidence records
  `(a, b, face)`: it is the lexicographic order, so equal `(a, b)` records are adjacent after sorting and
  the edge-multiplicity scan `e[j].a == e[i].a && e[j].b == e[i].b` sees every edge as one run.
-/
import Tess.C.SplitFind

namespace Tess.C

def ltl (x y : Nat × Nat × Nat) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 < y.2.2)))

/-- C `cmp` on `(a, b, face)`. -/
def incOrder (x y : Nat × Nat × Nat) : Int :=
  if x.1 ≠ y.1 then (if x.1 > y.1 then 1 else -1)
  else if x.2.1 ≠ y.2.1 then (if x.2.1 > y.2.1 then 1 else -1)
  else if x.2.2 > y.2.2 then 1 else if x.2.2 < y.2.2 then -1 else 0

theorem incOrder_spec (x y : Nat × Nat × Nat) :
    (incOrder x y = -1 ↔ ltl x y) ∧ (incOrder x y = 0 ↔ x = y) ∧ (incOrder x y = 1 ↔ ltl y x) := by
  obtain ⟨a, b, f⟩ := x; obtain ⟨c, d, g⟩ := y
  unfold incOrder ltl
  simp only [Prod.mk.injEq]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> by_cases h3 : f < g <;> by_cases h4 : f > g <;>
    by_cases h5 : a > c <;> by_cases h6 : b > d <;> simp [h1, h2, h3, h4, h5, h6] <;> omega

end Tess.C
