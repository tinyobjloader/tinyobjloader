import Tess.Check
namespace Tess

/-- Exact affine dual witnesses for an overlay cell. Every cell is the
intersection of six triangle half-planes. A nonnegative combination of those
half-planes and the constant one proves an affine bound throughout the cell.
The search is untrusted: its returned coefficients are independently checked. -/
def detColumns (a b c : Separator) : Rat :=
  a.x*(b.y*c.c-b.c*c.y)-b.x*(a.y*c.c-a.c*c.y)+c.x*(a.y*b.c-a.c*b.y)
def combine3 (a b c weights : Separator) : Separator :=
  (a.scale weights.x).add ((b.scale weights.y).add (c.scale weights.c))
def coneWitnessValid (a b c target weights : Separator) : Bool :=
  decide (0≤weights.x ∧ 0≤weights.y ∧ 0≤weights.c) && planesEqual (combine3 a b c weights) target

def coneTriple (a b c target : Separator) : Bool :=
  let d:=detColumns a b c
  if d=0 then false else
    coneWitnessValid a b c target
      ⟨detColumns target b c/d,detColumns a target c/d,detColumns a b target/d⟩
def coneCheck (lines : Array Separator) (target : Separator) : Bool :=
  (List.range lines.size).any fun k => (List.range k).any fun j => (List.range j).any fun i =>
    coneTriple lines[i]! lines[j]! lines[k]! target

def overlayHalfplanes (seed : ExactMesh) (a : Face) (output : ExactMesh) (b : Face) : Array Separator :=
  (((a.edges.map fun (i,j) => supportingLine (seed.project i) (seed.project j)) ++
    (b.edges.map fun (i,j) => supportingLine (output.project i) (output.project j))) ++ [(⟨0,0,1⟩ : Separator)]).toArray

def heightDifference (seed : ExactMesh) (a : Face) (output : ExactMesh) (b : Face) : Separator :=
  (heightPlane seed a).add (heightPlane output b).neg

def overlayPairBound (seed : ExactMesh) (a : Face) (output : ExactMesh) (b : Face) (tolerance : Rat) : Bool :=
  planesEqual (heightPlane seed a) (heightPlane output b) || noInteriorOverlap seed a output b ||
  (let lines:=overlayHalfplanes seed a output b
   let delta:=heightDifference seed a output b
   coneCheck lines (delta.add ⟨0,0,tolerance⟩) && coneCheck lines (delta.neg.add ⟨0,0,tolerance⟩))

def overlayBoundCheck (seed output : ExactMesh) (tolerance : Rat) : Bool :=
  seed.faces.all fun a => output.faces.all fun b =>
    (overlayPoints seed a output b).all fun p =>
      decide (-tolerance≤affineHeight seed a p-affineHeight output b p ∧
        affineHeight seed a p-affineHeight output b p≤tolerance)

def referenceBoundCheck (seed output : ExactMesh) (tolerance : Rat) : Bool :=
  decide (0≤tolerance) && overlayBoundCheck seed output tolerance &&
  seed.faces.all (fun a => output.faces.all fun b => overlayPairBound seed a output b tolerance)
end Tess
