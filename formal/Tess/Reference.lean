import Tess.Separation
namespace Tess

def Separator.scale (q : Rat) (l : Separator) : Separator := ⟨q*l.x,q*l.y,q*l.c⟩
def heightPlane (m : ExactMesh) (f : Face) : Separator :=
  let a := m.project f.a; let b := m.project f.b; let c := m.project f.c
  let ha := (m.point f.a).coord m.axis
  let hb := (m.point f.b).coord m.axis
  let hc := (m.point f.c).coord m.axis
  ((supportingLine b c).scale ha |>.add ((supportingLine c a).scale hb) |>.add
    ((supportingLine a b).scale hc)).scale (1/orient a b c)

def planesEqual (a b : Separator) : Bool := decide (a.x=b.x ∧ a.y=b.y ∧ a.c=b.c)
/-- A supporting edge of one positive triangle separates its open interior
from the other closed triangle. Tangential/collinear contacts are allowed. -/
def edgeSeparates (a : ExactMesh) (fa : Face) (b : ExactMesh) (fb : Face) : Bool :=
  fa.edges.any fun (x,y) => fb.ids.all fun i =>
    decide (orient (a.project x) (a.project y) (b.project i) ≤ 0)
def noInteriorOverlap (a : ExactMesh) (fa : Face) (b : ExactMesh) (fb : Face) : Bool :=
  edgeSeparates a fa b fb || edgeSeparates b fb a fa
/-- An independent sufficient exact-reference gate. It also avoids relying on
unproved completeness of overlay enumeration for the zero-tolerance proof. -/
def planeReferenceCheck (seed output : ExactMesh) : Bool :=
  seed.faces.all fun a => output.faces.all fun b =>
    planesEqual (heightPlane seed a) (heightPlane output b) || noInteriorOverlap seed a output b
end Tess
