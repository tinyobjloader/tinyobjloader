import Tess.AffineBound
namespace Tess

/-- Geometry-only view used by the fixed-boundary seed checker. Extended
provenance stays bound independently to the caller-held version-2 request. -/
def geometryView (m : ExactMesh) : ExactMesh :=
  { m with
    constraints := m.constraints.filterMap (fun e =>
      if e.kind=3 then
        if (implicitCreases m).any (fun original => original.a=e.a && original.b=e.b) then
          some ({a:=e.a,b:=e.b,kind:=2,source:=2^64-1} : Constraint) else none
      else some ({ a := e.a, b := e.b, kind := e.kind, source := e.source } : Constraint))
    vertexIds := #[]
    faceIds := #[] }
def seedCertificate (cert : Certificate2) : Certificate :=
  {cert.snapshot with seed:=geometryView cert.snapshot.seed,output:=geometryView cert.snapshot.seed}

def pointAt (a b : Point3) (t : Rat) : Point3 :=
  ⟨a.x+t*(b.x-a.x),a.y+t*(b.y-a.y),a.z+t*(b.z-a.z)⟩
def ownerSegments (m : ExactMesh) (owner : Nat) : List Constraint :=
  m.constraints.toList.filter fun e => e.owner=owner

def chainFrom (seed output : ExactMesh) (original : Constraint) : Nat → Rat → List Constraint → Bool
  | v,t,[] => decide (v=original.b ∧ t=1)
  | v,t,e::tail =>
    decide (e.a=v ∧ e.ta=t ∧ e.ta<e.tb ∧ e.tb≤1 ∧
      e.kind=original.kind ∧ e.source=original.source ∧ e.owner=original.owner ∧ e.tag=original.tag ∧
      e.a<output.points.size ∧ e.b<output.points.size ∧ e.a≠e.b ∧
      output.point e.a=pointAt (seed.point original.a) (seed.point original.b) e.ta ∧
      output.point e.b=pointAt (seed.point original.a) (seed.point original.b) e.tb) &&
    chainFrom seed output original e.b e.tb tail

def permittedSubdivision (run : RunRequest) (e : Constraint) : Bool :=
  if e.kind=1 then run.subdivideBoundary && (!run.ownerListMode || run.owners.contains e.owner)
  else run.subdivideFeatures

def extendedConstraints (cert : Certificate2) : Bool :=
  let seed:=cert.snapshot.seed; let output:=cert.snapshot.output
  decide ((seed.constraints.toList.map (·.owner)).Nodup) &&
  seed.constraints.all (fun e =>
    decide (e.a<seed.points.size ∧ e.b<seed.points.size ∧ e.a≠e.b ∧ e.ta=0 ∧ e.tb=1 ∧
      (e.kind=1 ∨ e.kind=2 ∨ e.kind=3)) &&
    (if e.kind=1 then decide (e.owner=e.a ∧ e.source=e.a) else true) &&
    (if e.kind=3 then decide (e.source=2^64-1) &&
      ((faceEdges seed).contains (e.a,e.b) || (faceEdges seed).contains (e.b,e.a)) else true) &&
    (let segments:=ownerSegments output e.owner
     if e.kind=2 && 0<cert.run.tolerance && segments.isEmpty then true else
       chainFrom seed output e e.a 0 segments &&
       (permittedSubdivision cert.run e || decide (segments.length=1)))) &&
  output.constraints.all (fun e =>
    seed.constraints.any (fun original => original.owner=e.owner) &&
    decide ((faceEdges output).count (e.a,e.b)=1 ∧
      (faceEdges output).count (e.b,e.a)=(if e.kind=1 then 0 else 1))) &&
  (ringEdges cert.snapshot.rings).all (fun (a,b) => seed.constraints.any fun e =>
    decide (e.a=a ∧ e.b=b ∧ e.kind=1 ∧ e.owner=a))

def expandedBoundary (cert : Certificate2) : List (Nat × Nat) :=
  (ringEdges cert.snapshot.rings).flatMap fun (a,_) =>
    (ownerSegments cert.snapshot.output a).filterMap fun e => if e.kind=1 then some (e.a,e.b) else none

def stableInputCheck (seed output : ExactMesh) : Bool :=
  decide (seed.points.size≤output.points.size ∧ seed.vertexIds.size=seed.points.size ∧
    output.vertexIds.size=output.points.size ∧ seed.faceIds.size=seed.faces.size ∧
    output.faceIds.size=output.faces.size ∧ output.vertexIds.toList.Nodup ∧ output.faceIds.toList.Nodup) &&
  allN seed.points.size (fun i => decide (seed.point i=output.point i ∧ seed.sources[i]?=some i ∧
    output.sources[i]?=some i ∧ seed.pinned[i]?=some true ∧ output.pinned[i]?=some true ∧
    seed.vertexIds[i]?=output.vertexIds[i]?))

/-- Version 2 checks the frozen seed, complete run request, ordered affine
constraint chains and stable IDs, and independently checks the output complex.
Its geometric soundness theorems are separate from optimizer quality claims. -/
def check2 (request cert : Certificate2) : Bool :=
  decide (request.snapshot.requestedAxis=cert.snapshot.requestedAxis ∧
    request.snapshot.strictPlanar=cert.snapshot.strictPlanar ∧ request.snapshot.rings=cert.snapshot.rings ∧
    request.snapshot.seed=cert.snapshot.seed ∧ request.run=cert.run ∧
    0<cert.run.targetArea ∧ 0≤cert.run.tolerance) &&
  check (seedCertificate request) (seedCertificate cert) &&
  decide (cert.snapshot.seed.axis=cert.snapshot.output.axis ∧ cert.snapshot.seed.u=cert.snapshot.output.u ∧
    cert.snapshot.seed.w=cert.snapshot.output.w ∧ cert.snapshot.seed.orientation=cert.snapshot.output.orientation) &&
  stableInputCheck cert.snapshot.seed cert.snapshot.output && extendedConstraints cert &&
  meshCheck cert.snapshot.rings cert.snapshot.output (expandedBoundary cert) &&
  decide (cert.snapshot.output.planar=planarCheck cert.snapshot.output) &&
  (if cert.snapshot.strictPlanar then planarCheck cert.snapshot.output else true) &&
  referenceBoundCheck cert.snapshot.seed cert.snapshot.output cert.run.tolerance

end Tess
