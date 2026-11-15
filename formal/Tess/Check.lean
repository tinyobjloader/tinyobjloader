import Tess.Reference
namespace Tess

def allN (n : Nat) (p : Nat → Bool) : Bool := (List.range n).all p
def facePositive (m : ExactMesh) (f : Face) : Bool :=
  f.ids.all (fun i => decide (i < m.points.size)) && positive (m.project f.a) (m.project f.b) (m.project f.c)
def inside (m : ExactMesh) (f : Face) (p : Point2) (strict : Bool := false) : Bool :=
  f.edges.all fun (a,b) => if strict then decide (0 < orient (m.project a) (m.project b) p)
    else decide (0 ≤ orient (m.project a) (m.project b) p)
def segmentConflict (m : ExactMesh) (a b c d : Nat) : Bool :=
  if (a=c && b=d) || (a=d && b=c) then false else
  let p := m.project a; let q := m.project b
  let r := m.project c; let s := m.project d
  (decide (c≠a ∧ c≠b) && onSegment p q r) ||
  (decide (d≠a ∧ d≠b) && onSegment p q s) ||
  (decide (a≠c ∧ a≠d) && onSegment r s p) ||
  (decide (b≠c ∧ b≠d) && onSegment r s q) ||
  decide (orient p q r * orient p q s < 0 ∧ orient r s p * orient r s q < 0)
def facePair (m : ExactMesh) (a b : Face) : Bool :=
  pairSeparable m a b && !(a.ids.any (fun i => inside m b (m.project i) true)) &&
  !(b.ids.any (fun i => inside m a (m.project i) true)) &&
  a.edges.all (fun (x,y) => b.edges.all fun (u,v) => !segmentConflict m x y u v)
def faceEdges (m : ExactMesh) : List (Nat × Nat) := m.faces.toList.flatMap Face.edges

def ringEdges (rings : Array Nat) : List (Nat × Nat) :=
  (List.range (rings.size-1)).flatMap fun r =>
    let start := rings[r]?.getD 0; let stop := rings[r+1]?.getD 0
    (List.range (stop-start)).map fun k => (start+k,if start+k+1=stop then start else start+k+1)
def orientedBoundary (rings : Array Nat) (_m : ExactMesh) : List (Nat × Nat) :=
  ringEdges rings
def balance (edges : List (Nat × Nat)) (a b : Nat) : Int :=
  (edges.count (a,b) : Int) - (edges.count (b,a) : Int)
def boundaryCheckEdges (expected : List (Nat × Nat)) (m : ExactMesh) : Bool :=
  let actual := faceEdges m
  (actual++expected).all fun (a,b) => decide (balance actual a b = balance expected a b)
def boundaryCheck (rings : Array Nat) (m : ExactMesh) : Bool := boundaryCheckEdges (ringEdges rings) m
def ringArea (rings : Array Nat) (m : ExactMesh) (r : Nat) : Rat :=
  let start := rings[r]?.getD 0; let stop := rings[r+1]?.getD 0
  (List.range (stop-start)).foldl (fun sum k =>
    let a := m.project (start+k)
    let b := m.project (if start+k+1=stop then start else start+k+1)
    sum + a.x*b.y - b.x*a.y) 0
/-- Half-open ray crossing. 2 denotes boundary, 1 inside, 0 outside. -/
def classifyRing (rings : Array Nat) (m : ExactMesh) (r : Nat) (p : Point2) : Nat := Id.run do
  let start := rings[r]?.getD 0; let stop := rings[r+1]?.getD 0
  let mut result := false
  for k in [:stop-start] do
    let a := m.project (start+k)
    let b := m.project (if start+k+1=stop then start else start+k+1)
    if onSegment a b p then return 2
    let side := orient a b p
    if (a.y ≤ p.y && p.y < b.y && 0 < side) || (b.y ≤ p.y && p.y < a.y && side < 0) then
      result := !result
  return if result then 1 else 0

def domainCheck (rings : Array Nat) (m : ExactMesh) : Bool :=
  let nr := rings.size-1
  let edges := ringEdges rings
  decide (0 < nr ∧ rings[0]?.getD 1 = 0 ∧ rings[nr]?.getD 0 ≤ m.points.size) &&
  allN nr (fun r => decide (rings[r]?.getD 0 + 3 ≤ rings[r+1]?.getD 0)) &&
  allN rings.size (fun r => decide (rings[r]?.getD 0 ≤ m.points.size)) &&
  decide (0 < ringArea rings m 0) &&
  allN (nr-1) (fun i => decide (ringArea rings m (i+1) < 0)) &&
  allN (rings[nr]?.getD 0) (fun a => allN a fun b => decide (m.project a ≠ m.project b)) &&
  edges.all (fun (a,b) => edges.all fun (c,d) => !segmentConflict m a b c d) &&
  allN (nr-1) (fun i =>
    let p := m.project (rings[i+1]?.getD 0)
    decide (classifyRing rings m 0 p = 1) &&
    allN (nr-1) (fun j => if i=j then true else decide (classifyRing rings m (j+1) p = 0)))

def planeValue (m : ExactMesh) (f : Face) (p : Point3) : Rat :=
  let a := m.point f.a; let b := m.point f.b; let c := m.point f.c
  let ax := a.x-p.x; let ay := a.y-p.y; let az := a.z-p.z
  let bx := b.x-p.x; let byy := b.y-p.y; let bz := b.z-p.z
  let cx := c.x-p.x; let cy := c.y-p.y; let cz := c.z-p.z
  ax*(byy*cz-bz*cy)-ay*(bx*cz-bz*cx)+az*(bx*cy-byy*cx)
def planarCheck (m : ExactMesh) : Bool :=
  match m.faces[0]? with
  | none => false
  | some f => m.points.all fun p => decide (planeValue m f p = 0)

def adjacent (a b : Face) : Bool := a.edges.any fun (x,y) => b.edges.contains (y,x)
private def connectedFaces (m : ExactMesh) : Bool := Id.run do
  if m.faces.isEmpty then return false
  let mut visited := Array.replicate m.faces.size false
  let mut queue := #[0]
  visited := visited.set! 0 true
  let mut front := 0
  for _ in [:m.faces.size] do
    if front < queue.size then
      let f := m.faces[queue[front]!]!
      front := front+1
      for j in [:m.faces.size] do
        if !visited[j]! && adjacent f m.faces[j]! then
          visited := visited.set! j true
          queue := queue.push j
  return visited.all id
private def vertexLink (m : ExactMesh) (v : Nat) : Bool := Id.run do
  let mut edges := #[]
  for f in m.faces do
    if f.a=v then edges := edges.push (f.b,f.c)
    if f.b=v then edges := edges.push (f.c,f.a)
    if f.c=v then edges := edges.push (f.a,f.b)
  if edges.isEmpty then return false
  let mut degrees := Array.replicate m.points.size 0
  for (a,b) in edges do
    degrees := degrees.modify a (·+1)
    degrees := degrees.modify b (·+1)
  let boundary := m.constraints.any fun e => e.kind=1 && (e.a=v || e.b=v)
  let ends := degrees.toList.count 1
  if (if boundary then ends != 2 else ends != 0) then return false
  if !degrees.all (fun n => n=0 || n=1 || n=2) then return false
  let mut reached := Array.replicate m.points.size false
  reached := reached.set! edges[0]!.1 true
  for _ in [:m.points.size] do
    for (a,b) in edges do
      if reached[a]! || reached[b]! then
        reached := reached.set! a true
        reached := reached.set! b true
  return allN m.points.size fun i => (degrees[i]?.getD 0 = 0) || reached[i]?.getD false

def topologyCheck (rings : Array Nat) (m : ExactMesh) : Bool :=
  let edges := faceEdges m
  let undirected := edges.map fun (a,b) => if a<b then (a,b) else (b,a)
  edges.all (fun e => decide (edges.count e ≤ 1)) &&
  allN m.points.size (vertexLink m) && connectedFaces m &&
  decide (m.points.size + m.faces.size + rings.size-1 = undirected.eraseDups.length+2)

def meshCheck (rings : Array Nat) (m : ExactMesh) (expected : List (Nat × Nat) := ringEdges rings) : Bool :=
  decide (m.axis<3 ∧ m.u<3 ∧ m.w<3 ∧ m.u≠m.w ∧ m.u≠m.axis ∧ m.w≠m.axis) &&
  decide (m.u=(if m.orientation then (m.axis+1)%3 else (m.axis+2)%3) ∧
          m.w=(if m.orientation then (m.axis+2)%3 else (m.axis+1)%3)) &&
  m.faces.all (facePositive m) &&
  allN m.faces.size (fun i => allN i fun j => facePair m m.faces[i]! m.faces[j]!) &&
  boundaryCheckEdges expected m && topologyCheck rings m

def affineHeight (m : ExactMesh) (f : Face) (p : Point2) : Rat :=
  let a := m.project f.a; let b := m.project f.b; let c := m.project f.c
  (orient p b c * (m.point f.a).coord m.axis +
   orient p c a * (m.point f.b).coord m.axis +
   orient p a b * (m.point f.c).coord m.axis) / orient a b c
private def properCrossing (p q r s : Point2) : Option Point2 :=
  let x := orient r s p; let y := orient r s q
  if x*y<0 then
    let t := x/(x-y)
    some ⟨p.x+t*(q.x-p.x),p.y+t*(q.y-p.y)⟩
  else none
def overlayPoints (a : ExactMesh) (fa : Face) (b : ExactMesh) (fb : Face) : List Point2 :=
  let vertices := fa.ids.map a.project ++ fb.ids.map b.project
  let crossings := fa.edges.flatMap fun (u,v) => fb.edges.filterMap fun (x,y) =>
    properCrossing (a.project u) (a.project v) (b.project x) (b.project y)
  (vertices++crossings).filter fun p => inside a fa p && inside b fb p

def overlayCheck (seed output : ExactMesh) : Bool :=
  seed.faces.all fun a => output.faces.all fun b =>
    (overlayPoints seed a output b).all fun p => decide (affineHeight seed a p = affineHeight output b p)

def referenceCheck (seed output : ExactMesh) : Bool :=
  overlayCheck seed output && planeReferenceCheck seed output

def sameRequest (request cert : Certificate) : Bool :=
  decide ((request.requestedAxis=cert.requestedAxis ∧ request.strictPlanar=cert.strictPlanar ∧
          request.rings=cert.rings ∧ request.seed.points=cert.seed.points) ∧ request.seed=cert.seed)
def implicitCreases (seed : ExactMesh) : List Constraint :=
  (seed.faces.toList.flatMap fun f => f.edges.filterMap fun (a,b) =>
    if seed.faces.any (fun g => g.edges.contains (b,a) &&
        g.ids.any (fun i => decide (planeValue seed f (seed.point i) ≠ 0))) then
      some {a:=min a b,b:=max a b,kind:=2,source:=2^64-1} else none).eraseDups

def constraintCheck (cert : Certificate) : Bool :=
  let seed := cert.seed; let output := cert.output
  let expected := ((ringEdges cert.rings).map fun (a,b) => ({a,b,kind:=1,source:=a} : Constraint)) ++ implicitCreases seed
  -- Boundary provenance uses the boundary vertex's stable input ID.
  decide (expected.length=seed.constraints.size) &&
  expected.all (fun e => seed.constraints.toList.contains e) &&
  seed.constraints.all (fun e => decide (e.a<seed.points.size ∧ e.b<seed.points.size ∧ e.a≠e.b ∧ (e.kind=1 ∨ e.kind=2))) &&
  decide (seed.constraints=output.constraints) &&
  seed.constraints.all (fun e => (faceEdges output).contains (e.a,e.b) || (faceEdges output).contains (e.b,e.a)) &&
  decide (seed.points.size≤output.points.size) &&
  allN seed.points.size (fun i => decide (seed.point i=output.point i ∧ seed.sources[i]?=some i ∧
    output.sources[i]?=some i ∧ seed.pinned[i]?=some true ∧ output.pinned[i]?=some true))

def check (request cert : Certificate) : Bool :=
  sameRequest request cert &&
  decide (cert.seed.points.size = cert.rings[cert.rings.size-1]?.getD 0) &&
  decide (cert.requestedAxis=0 ∨ cert.seed.axis+1=cert.requestedAxis) &&
  decide (cert.seed.axis=cert.output.axis ∧ cert.seed.u=cert.output.u ∧ cert.seed.w=cert.output.w ∧
    cert.seed.orientation=cert.output.orientation) &&
  domainCheck cert.rings cert.seed && meshCheck cert.rings cert.seed &&
  meshCheck cert.rings cert.output && constraintCheck cert &&
  decide (cert.seed.planar=planarCheck cert.seed ∧ cert.output.planar=planarCheck cert.output) &&
  (if cert.strictPlanar then planarCheck cert.seed else true) && referenceCheck cert.seed cert.output
end Tess
