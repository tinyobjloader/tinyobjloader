import Tess.SegmentConflict
import Tess.Orient3
import Tess.TriangleContact

/-! Bounded exact-rational validation protocol, separate from certificates.
Ordinary records have an operation and eight signed-decimal numerator/denominator
coordinates. `orient3` carries four 3D points as twelve coordinates.
`indexedsegments` carries eight 2D coordinates plus four nonnegative vertex IDs;
repeated IDs denote the same vertex and must carry the same coordinates.
This parser is a test boundary, not a verified C refinement. -/
namespace Tess.PredicateFixture

def decodeRational (text : String) : Except String Rat := do
  match text.splitOn "/" with
  | [numerator,denominator] =>
    if numerator.length>1024 || denominator.length>1024 then
      throw "resource limit: rational digits"
    let n ← match numerator.toInt? with
      | some n => pure n | none => throw "invalid numerator"
    let d ← match denominator.toNat? with
      | some d => pure d | none => throw "invalid denominator"
    if d=0 then throw "zero denominator"
    return (n : Rat)/(d : Rat)
  | _ => throw "expected numerator/denominator"

def decode3D (fields : Array String) : Except String (Array Point3) := do
  if fields.size != 12 then throw "expected twelve coordinates"
  let mut coordinates := #[]
  for field in fields do coordinates := coordinates.push (← decodeRational field)
  let point (i : Nat) : Point3 := ⟨coordinates[3*i]!, coordinates[3*i+1]!, coordinates[3*i+2]!⟩
  return #[point 0, point 1, point 2, point 3]

def decodePointArray (fields : Array String) (count : Nat) : Except String (Array Point3) := do
  if fields.size != 3 * count then throw "expected eighteen coordinates"
  let mut coordinates := #[]
  for field in fields do coordinates := coordinates.push (← decodeRational field)
  let mut points := #[]
  for i in [:count] do
    points := points.push ⟨coordinates[3*i]!, coordinates[3*i+1]!, coordinates[3*i+2]!⟩
  return points

def decodeIndex (text : String) : Except String Nat := do
  if text.length=0 || text.length>10 then throw "invalid vertex index"
  match text.toNat? with
  | some index =>
      if index≥1024 then throw "resource limit: vertex index"
      return index
  | none => throw "invalid vertex index"

def sign (q : Rat) : Int := if 0<q then 1 else if q=0 then 0 else -1

def evaluate (operation : String) (coordinates : Array Rat) : Except String Int := do
  if coordinates.size≠8 then throw "expected eight coordinates"
  let point (i : Nat) : Point2 := ⟨coordinates[2*i]!,coordinates[2*i+1]!⟩
  let a:=point 0; let b:=point 1; let c:=point 2; let d:=point 3
  match operation with
  | "orient2" => return sign (orient a b c)
  | "incircle" => return sign (incircleDet a b c d * orient a b c)
  | "segments" => return if closedIntersection a b c d then 1 else 0
  | "onsegment" => return if onSegment a b c then 1 else 0
  | _ => throw "unknown predicate"

def evaluate3D (operation : String) (points : Array Point3) : Except String Int := do
  if points.size≠4 then throw "expected four points"
  match operation with
  | "orient3" => return sign (orient3 points[0]! points[1]! points[2]! points[3]!)
  | _ => throw "unknown 3D predicate"

/-- Build the finite exact-coordinate mesh used by the indexed predicate.
Out-of-range IDs, or inconsistent coordinates for a repeated ID, are rejected. -/
def indexedMesh (coordinates : Array Rat) (ids : Array Nat) : Except String ExactMesh := do
  if coordinates.size≠8 then throw "expected eight coordinates"
  if ids.size≠4 then throw "expected four vertex indices"
  let size := ids.foldl max 0 + 1
  let mut points := Array.replicate size (default : Point3)
  let mut seen := Array.replicate size false
  for i in [:4] do
    let index := ids[i]!
    let point : Point3 := ⟨coordinates[2*i]!, coordinates[2*i+1]!, 0⟩
    if seen[index]! then
      if points[index]! != point then
        throw "inconsistent coordinates for repeated vertex index"
    else
      points := points.set! index point
      seen := seen.set! index true
  return {
    points
    sources := Array.replicate size 0
    pinned := Array.replicate size false
    faces := #[]
    constraints := #[]
    axis := 2
    u := 0
    w := 1
    orientation := true
    planar := true
  }

def evaluateAudit (operation : String) (fields : Array String) : Except String Int := do
  match operation with
  | "tricontact" =>
      let points ← decodePointArray fields 6
      return if noncoplanarTrianglesConflict points[0]! points[1]! points[2]! points[3]! points[4]! points[5]! then 0 else 1
  | _ => throw "unknown audit predicate"

def evaluateIndexed (operation : String) (coordinates : Array Rat)
    (ids : Array Nat) : Except String Int := do
  match operation with
  | "indexedsegments" =>
      match ids.toList with
      | [a, b, c, d] =>
          let mesh ← indexedMesh coordinates ids
          return if segmentConflict mesh a b c d then 1 else 0
      | _ => throw "expected four vertex indices"
  | _ => throw "unknown indexed predicate"

def decodeLine (line : String) : Except String Int := do
  if line.length>32768 then throw "resource limit: line"
  let words := (line.splitOn " ").filter (fun word => !word.isEmpty)
  match words with
  | operation :: fields =>
    if operation="orient3" then
      evaluate3D operation (← decode3D fields.toArray)
    else if operation="tricontact" then
      evaluateAudit operation fields.toArray
    else if operation="indexedsegments" then
      if fields.length≠12 then throw "expected eight coordinates and four indices"
      let mut coordinates := #[]
      for field in fields.take 8 do coordinates:=coordinates.push (← decodeRational field)
      let mut ids := #[]
      for field in fields.drop 8 do ids:=ids.push (← decodeIndex field)
      evaluateIndexed operation coordinates ids
    else
      if fields.length≠8 then throw "expected eight coordinates"
      let mut coordinates := #[]
      for field in fields do coordinates:=coordinates.push (← decodeRational field)
      evaluate operation coordinates
  | [] => throw "empty predicate line"

/-- A fixture sign uses the same strict orientation convention as the kernel
specification. The parser and runtime boundary remain separate. -/
theorem positive_sign (a b c : Point2) :
    sign (orient a b c)=1 ↔ positive a b c=true := by
  by_cases hpos : 0<orient a b c <;> by_cases hzero : orient a b c=0 <;>
    simp [sign,positive,hpos,hzero]

end Tess.PredicateFixture
