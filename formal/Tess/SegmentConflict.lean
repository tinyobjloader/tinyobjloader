import Tess.Certificate

namespace Tess

/-! Computational definition of indexed segment conflict.
This module is intentionally light enough for executable predicate probes. -/

def segmentConflict (m : ExactMesh) (a b c d : Nat) : Bool :=
  if (a=c && b=d) || (a=d && b=c) then false else
  let p := m.project a; let q := m.project b
  let r := m.project c; let s := m.project d
  (decide (c≠a ∧ c≠b) && onSegment p q r) ||
  (decide (d≠a ∧ d≠b) && onSegment p q s) ||
  (decide (a≠c ∧ a≠d) && onSegment r s p) ||
  (decide (b≠c ∧ b≠d) && onSegment r s q) ||
  decide (orient p q r * orient p q s < 0 ∧ orient r s p * orient r s q < 0)
end Tess
