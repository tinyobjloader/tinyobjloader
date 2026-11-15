import Tess.Certificate
namespace Tess

structure Separator where
  x : Rat
  y : Rat
  c : Rat
  deriving Repr, Inhabited

def Separator.value (line : Separator) (p : Point2) : Rat := line.x*p.x+line.y*p.y+line.c
def Separator.neg (line : Separator) : Separator := ⟨-line.x,-line.y,-line.c⟩
def Separator.add (a b : Separator) : Separator := ⟨a.x+b.x,a.y+b.y,a.c+b.c⟩
def supportingLine (a b : Point2) : Separator := ⟨a.y-b.y,b.x-a.x,a.x*b.y-a.y*b.x⟩
def commonIds (a b : Face) : List Nat := (a.ids.filter b.ids.contains).eraseDups

def separatorValid (m : ExactMesh) (a b : Face) (line : Separator) : Bool :=
  decide ((commonIds a b).length≤2) &&
  a.ids.all (fun i => if b.ids.contains i then decide (line.value (m.project i)=0)
      else decide (0<line.value (m.project i))) &&
  b.ids.all (fun i => if a.ids.contains i then decide (line.value (m.project i)=0)
      else decide (line.value (m.project i)<0))
private def weakSeparator (m : ExactMesh) (a b : Face) (line : Separator) : Bool :=
  a.ids.all (fun i => decide (0≤line.value (m.project i))) &&
  b.ids.all (fun i => decide (line.value (m.project i)≤0))
private def candidates (m : ExactMesh) (a b : Face) : List Separator :=
  ((a.edges++b.edges).map fun (x,y) => supportingLine (m.project x) (m.project y)).flatMap fun l => [l,l.neg]

def findSeparator (m : ExactMesh) (a b : Face) : Option Separator :=
  if (commonIds a b).isEmpty then
    (candidates m a b).findSome? fun line =>
      let av := a.ids.map fun i => line.value (m.project i)
      let bv := b.ids.map fun i => line.value (m.project i)
      let low := av.foldl min (av.headD 0)
      let high := bv.foldl max (bv.headD 0)
      let shifted := {line with c := line.c-(low+high)/2}
      if separatorValid m a b shifted then some shifted else none
  else
    let line := ((candidates m a b).filter (weakSeparator m a b)).foldl Separator.add default
    if separatorValid m a b line then some line else none

def pairSeparable (m : ExactMesh) (a b : Face) : Bool :=
  match findSeparator m a b with
  | none => false
  | some line => separatorValid m a b line

/-- Acceptance retains a concrete rational separating affine functional.
The real-geometric convex-combination proof is supplied separately. -/
theorem pairSeparable_witness (m : ExactMesh) (a b : Face)
    (h : pairSeparable m a b = true) : ∃ line, separatorValid m a b line = true := by
  unfold pairSeparable at h
  cases found : findSeparator m a b with
  | none => simp [found] at h
  | some line => exact ⟨line,by simpa [found] using h⟩
end Tess
