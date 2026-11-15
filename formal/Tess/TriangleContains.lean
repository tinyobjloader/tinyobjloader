import Tess.Predicates

namespace Tess

/-- Exact 2D triangle containment: the three edge signs are either all
nonnegative or all nonpositive. Face orientation does not matter, matching the
project-axis branch of the 3D auditor. -/
def contains2 (a b c p : Point2) : Bool :=
  let first := orient a b p
  let second := orient b c p
  let third := orient c a p
  (0 ≤ first && 0 ≤ second && 0 ≤ third) ||
  (first ≤ 0 && second ≤ 0 && third ≤ 0)
end Tess
