import Tess.TriangleContact
import Tess.SegmentConflict

namespace Tess

/-! Executable Lean specification of the pairwise decision of the C 3D auditor
`tg_audit3_mode` (`lib/tess/src/audit.c`), including the coplanar branch and the
indexed shared-simplex allowance (`allowed`). It follows the C control flow
statement by statement so that it can be compared with the C diagnostic mode on
shared fixtures. It is a specification, not a refinement proof of the C code. -/

namespace PairAudit

def facePoint (m : ExactMesh) (f : Face) (k : Nat) : Point3 :=
  m.point (if k = 0 then f.a else if k = 1 then f.b else f.c)

def faceId (f : Face) (k : Nat) : Nat := if k = 0 then f.a else if k = 1 then f.b else f.c

/-- Projection axis of a nondegenerate face (`project` in C). -/
def projAxis (m : ExactMesh) (f : Face) : Option Nat :=
  firstProjectionAxis (m.point f.a) (m.point f.b) (m.point f.c)

/-- C `contains`: no mixed projected edge-orientation sign (orientation independent). -/
def containsPt (m : ExactMesh) (f : Face) (axis : Nat) (p : Point3) : Bool :=
  containsProject axis (m.point f.a) (m.point f.b) (m.point f.c) p

/-- Identifiers common to both faces, in the C scan order `i` over `a`, `j` over `b`. -/
def commonIds (fa fb : Face) : List Nat :=
  ((List.range 3).flatMap fun i => (List.range 3).filterMap fun j =>
    if faceId fa i = faceId fb j then some (faceId fa i) else none)

def between3 (x y p : Rat) : Bool :=
  if x ≤ y then decide (x ≤ p ∧ p ≤ y) else decide (y ≤ p ∧ p ≤ x)

/-- C `allowed`: the contact point is a shared vertex, or lies on the shared edge
(two shared identifiers: coordinate box and exact collinearity). -/
def allowed (m : ExactMesh) (fa fb : Face) (p : Point3) : Bool :=
  let common := commonIds fa fb
  if common.any (fun id => m.point id == p) then true
  else match common with
    | [i, j] =>
        let x := m.point i; let y := m.point j
        let da := Point3.mk (p.x - x.x) (p.y - x.y) (p.z - x.z)
        let db := Point3.mk (y.x - x.x) (y.y - x.y) (y.z - x.z)
        let box := between3 x.x y.x p.x && between3 x.y y.y p.y && between3 x.z y.z p.z
        let c0 := da.y * db.z - da.z * db.y
        let c1 := da.z * db.x - da.x * db.z
        let c2 := da.x * db.y - da.y * db.x
        box && decide (c0 = 0 ∧ c1 = 0 ∧ c2 = 0)
    | _ => false

/-- C `edges_against(a, b, projection)`: edge endpoint and strict-cut contacts that are not allowed. -/
def edgesAgainst (m : ExactMesh) (fa fb : Face) (axis : Nat) : Bool :=
  (List.range 3).all fun i =>
    let xi := faceId fa i; let yi := faceId fa ((i + 1) % 3)
    let x := m.point xi; let y := m.point yi
    let dx := planeValue m fb x; let dy := planeValue m fb y
    let c1 := !(dx = 0 && containsPt m fb axis x && !allowed m fa fb x)
    let c2 := !(dy = 0 && containsPt m fb axis y && !allowed m fa fb y)
    let c3 := if dx * dy < 0 then
        let p := segment3Point x y (dx / (dx - dy))
        !(containsPt m fb axis p && !allowed m fa fb p)
      else true
    c1 && c2 && c3

/-- Mesh with the auditor's `u,w` set for a projection axis. -/
def withAxis (m : ExactMesh) (pa : Nat) : ExactMesh := { m with u := (pa + 1) % 3, w := (pa + 2) % 3 }

def sharedCount (fa fb : Face) : Nat :=
  (List.range 3).foldl (fun s k => s + (List.range 3).foldl
    (fun t l => t + if faceId fa k = faceId fb l then 1 else 0) 0) 0

/-- Pair decision: `true` when the pair is accepted (no forbidden contact). -/
def pairOk (m : ExactMesh) (fa fb : Face) : Bool :=
  match projAxis m fa, projAxis m fb with
  | some pa, some pb =>
      let coplanar := (List.range 3).all fun k => planeValue m fa (facePoint m fb k) = 0
      if coplanar then
        let mu := withAxis m pa
        let pts := (List.range 3).all fun k =>
          let x := facePoint m fa k; let y := facePoint m fb k
          !(containsPt m fb pa x && !allowed m fa fb x) &&
          !(containsPt m fa pa y && !allowed m fa fb y)
        let segs := (List.range 3).all fun k => (List.range 3).all fun l =>
          !(segmentConflict mu (faceId fa k) (faceId fa ((k + 1) % 3))
              (faceId fb l) (faceId fb ((l + 1) % 3)))
        pts && segs && decide (sharedCount fa fb ≠ 3)
      else
        edgesAgainst m fa fb pb && edgesAgainst m fb fa pa
  | _, _ => false

end PairAudit
end Tess
