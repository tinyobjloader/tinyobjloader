import Tess.Certificate

namespace Tess

/-! Light executable specification of the 3D orientation determinant.
It uses the same row order as `tg_orient3`: rows are `a-d`, `b-d`, `c-d`. -/
def orient3 (a b c d : Point3) : Rat :=
  let ax := a.x-d.x; let ay := a.y-d.y; let az := a.z-d.z
  let bx := b.x-d.x; let byy := b.y-d.y; let bz := b.z-d.z
  let cx := c.x-d.x; let cy := c.y-d.y; let cz := c.z-d.z
  ax*(byy*cz-bz*cy) - ay*(bx*cz-bz*cx) + az*(bx*cy-byy*cx)
end Tess
