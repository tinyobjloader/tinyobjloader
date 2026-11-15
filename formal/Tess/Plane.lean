import Tess.Certificate

namespace Tess

/-! Light executable 3D plane and plane-cut definitions.
These modules are shared by the exact checker and bounded probes. -/

def planeValue (m : ExactMesh) (f : Face) (p : Point3) : Rat :=
  let a := m.point f.a; let b := m.point f.b; let c := m.point f.c
  let ax := a.x-p.x; let ay := a.y-p.y; let az := a.z-p.z
  let bx := b.x-p.x; let byy := b.y-p.y; let bz := b.z-p.z
  let cx := c.x-p.x; let cy := c.y-p.y; let cz := c.z-p.z
  ax*(byy*cz-bz*cy)-ay*(bx*cz-bz*cx)+az*(bx*cy-byy*cx)

def segment3Point (a b : Point3) (t : Rat) : Point3 :=
  ⟨a.x+t*(b.x-a.x), a.y+t*(b.y-a.y), a.z+t*(b.z-a.z)⟩

/-- Parameter of a strict plane crossing along `x -> y`, matching the
exact branch used by the 3D auditor. Callers must establish nonzero signs and
opposite signs before relying on it. -/
def planeCutParameter (m : ExactMesh) (f : Face) (x y : Nat) : Rat :=
  let dx := planeValue m f (m.point x)
  let dy := planeValue m f (m.point y)
  dx/(dx-dy)

def planeCutPoint (m : ExactMesh) (x y : Nat) (t : Rat) : Point3 :=
  segment3Point (m.point x) (m.point y) t

/-- Strict crossing insertions only; coplanar segments and endpoint/touching
contacts are handled by the surrounding audit, not this branch. -/
def planeCut (m : ExactMesh) (f : Face) (x y : Nat) : Option Point3 :=
  let dx := planeValue m f (m.point x)
  let dy := planeValue m f (m.point y)
  if dx*dy<0 then some (planeCutPoint m x y (dx/(dx-dy))) else none
end Tess
