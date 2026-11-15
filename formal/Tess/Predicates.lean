import Obj.Real

/-! Exact rational predicate specification for lib/tess. These theorems concern
    the executable specification; C refinement and domain coverage are separate
    obligations. No tolerance participates in a topological sign. -/
namespace Tess
structure Point2 where
  x : Rat
  y : Rat
  deriving DecidableEq, Repr

def orient (a b c : Point2) : Rat :=
  (b.x-a.x)*(c.y-a.y) - (b.y-a.y)*(c.x-a.x)

def positive (a b c : Point2) : Bool := decide (0 < orient a b c)
def collinear (a b c : Point2) : Bool := decide (orient a b c = 0)

theorem positive_sound (a b c : Point2) :
    positive a b c = true → 0 < orient a b c := by
  simp [positive]

theorem collinear_sound (a b c : Point2) :
    collinear a b c = true ↔ orient a b c = 0 := by
  simp [collinear]

def between (a b x : Rat) : Prop := (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)
instance (a b x : Rat) : Decidable (between a b x) := inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))
def onSegment (a b p : Point2) : Bool :=
  collinear a b p && decide (between a.x b.x p.x ∧ between a.y b.y p.y)

theorem onSegment_sound (a b p : Point2) :
    onSegment a b p = true →
    orient a b p = 0 ∧ between a.x b.x p.x ∧ between a.y b.y p.y := by
  simp [onSegment, collinear]

/-- Closed intersection includes endpoints and collinear overlaps. -/
def closedIntersection (a b c d : Point2) : Bool :=
  onSegment a b c || onSegment a b d || onSegment c d a || onSegment c d b ||
  decide (orient a b c * orient a b d < 0 ∧ orient c d a * orient c d b < 0)

def incircleDet (a b c d : Point2) : Rat :=
  let ax := a.x-d.x; let ay := a.y-d.y
  let bx := b.x-d.x; let byy := b.y-d.y
  let cx := c.x-d.x; let cy := c.y-d.y
  (ax*ax+ay*ay)*(bx*cy-byy*cx) -
  (bx*bx+byy*byy)*(ax*cy-ay*cx) +
  (cx*cx+cy*cy)*(ax*byy-ay*bx)

/-- The determinant is corrected by orientation; cocircular ties are retained. -/
def illegalDelaunay (a b c d : Point2) : Bool :=
  decide (0 < incircleDet a b c d * orient a b c)

theorem illegalDelaunay_sound (a b c d : Point2) :
    illegalDelaunay a b c d = true → 0 < incircleDet a b c d * orient a b c := by
  simp [illegalDelaunay]

example : positive ⟨0,0⟩ ⟨1,0⟩ ⟨0,1⟩ = true := by decide +kernel
example : onSegment ⟨0,0⟩ ⟨2,0⟩ ⟨1,0⟩ = true := by decide +kernel
example : closedIntersection ⟨0,0⟩ ⟨2,0⟩ ⟨1,0⟩ ⟨3,0⟩ = true := by decide +kernel
example : illegalDelaunay ⟨0,0⟩ ⟨1,0⟩ ⟨1,1⟩ ⟨0,1⟩ = false := by decide +kernel
#print axioms positive_sound
#print axioms onSegment_sound
end Tess
