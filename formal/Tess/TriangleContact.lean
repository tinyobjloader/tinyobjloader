import Tess.Orient3
import Tess.Plane
import Tess.Projection

namespace Tess

/-- Plane offset of point `p` from triangle `a b c`, using the same row order
as `tg_orient3`. -/
def pointPlaneValue (a b c p : Point3) : Rat := orient3 a b c p

/-- First axis on which the projected face is nondegenerate. -/
def firstProjectionAxis (a b c : Point3) : Option Nat :=
  if orient (projectPoint3 0 a) (projectPoint3 0 b) (projectPoint3 0 c) ≠ 0 then
    some 0
  else if orient (projectPoint3 1 a) (projectPoint3 1 b) (projectPoint3 1 c) ≠ 0 then
    some 1
  else if orient (projectPoint3 2 a) (projectPoint3 2 b) (projectPoint3 2 c) ≠ 0 then
    some 2
  else none

/-- Projected nondegenerate triangle containment. Degenerate faces have no
meaningful projected classification; callers reject them separately. -/
def containsNondegenerate (a b c p : Point3) : Bool :=
  match firstProjectionAxis a b c with
  | some axis => containsProject axis a b c p
  | none => false



/-- Contact between source edge `x-y` and a target triangle.
Endpoint touches and strict edge/plane cuts are both accepted. -/
def edgeAgainstTriangle (a b c x y : Point3) : Bool :=
  let dx := pointPlaneValue a b c x
  let dy := pointPlaneValue a b c y
  if dx = 0 then containsNondegenerate a b c x
  else if dy = 0 then containsNondegenerate a b c y
  else if dx * dy < 0 then
    containsNondegenerate a b c (segment3Point x y (dx / (dx - dy)))
  else false

/-- Exact contact test for two nondegenerate, noncoplanar 3D triangles.
This does not implement the auditor's permitted indexed shared-simplex
exception; callers with indexed faces must account for that separately. -/
def noncoplanarTrianglesConflict (a b c d e f : Point3) : Bool :=
  match firstProjectionAxis a b c, firstProjectionAxis d e f with
  | some _, some _ =>
      if pointPlaneValue a b c d = 0 && pointPlaneValue a b c e = 0 &&
         pointPlaneValue a b c f = 0 then
        false
      else
        edgeAgainstTriangle d e f a b ||
        edgeAgainstTriangle d e f b c ||
        edgeAgainstTriangle d e f c a ||
        edgeAgainstTriangle a b c d e ||
        edgeAgainstTriangle a b c e f ||
        edgeAgainstTriangle a b c f d
  | _, _ => false
end Tess
