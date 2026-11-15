import Tess.Predicates

/-! Bounded, versioned certificate decoder. Parsing/IO is outside the eventual
    geometric soundness theorem, which applies to the decoded artifact. -/
namespace Tess
structure Point3 where
  x : Rat
  y : Rat
  z : Rat
  deriving DecidableEq, Repr, Inhabited

def Point3.coord (p : Point3) (axis : Nat) : Rat :=
  if axis = 0 then p.x else if axis = 1 then p.y else p.z

structure Face where
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr, Inhabited

def Face.ids (f : Face) : List Nat := [f.a,f.b,f.c]
def Face.edges (f : Face) : List (Nat × Nat) := [(f.a,f.b),(f.b,f.c),(f.c,f.a)]
structure Constraint where
  a : Nat
  b : Nat
  kind : Nat
  source : Nat
  owner : Nat := 0
  ta : Rat := 0
  tb : Rat := 1
  tag : Nat := 0
  deriving DecidableEq, Repr, Inhabited
structure ExactMesh where
  points : Array Point3
  sources : Array Nat
  pinned : Array Bool
  faces : Array Face
  constraints : Array Constraint
  axis : Nat
  u : Nat
  w : Nat
  orientation : Bool
  planar : Bool
  vertexIds : Array Nat := #[]
  faceIds : Array Nat := #[]
  deriving DecidableEq, Repr
def ExactMesh.point (m : ExactMesh) (i : Nat) : Point3 := m.points[i]?.getD default
def ExactMesh.project (m : ExactMesh) (i : Nat) : Point2 :=
  let p := m.point i
  ⟨p.coord m.u,p.coord m.w⟩
structure Certificate where
  requestedAxis : Nat -- 0 automatic, 1..3 explicit
  strictPlanar : Bool
  rings : Array Nat
  seed : ExactMesh
  output : ExactMesh
  deriving DecidableEq, Repr
structure RunRequest where
  targetCount : Nat
  targetArea : Rat
  tolerance : Rat
  subdivideBoundary : Bool
  subdivideFeatures : Bool
  ownerListMode : Bool
  owners : Array Nat
  qualityBits : Array Nat
  maxPasses : Nat
  maxEdits : Nat
  maxCandidates : Nat
  resourceCaps : Array Nat
  deriving DecidableEq, Repr
structure Certificate2 where
  snapshot : Certificate
  run : RunRequest
  deriving DecidableEq, Repr
structure DecodeLimits where
  maxBytes : Nat := 16777216
  maxVertices : Nat := 10000
  maxFaces : Nat := 20000
  maxHexDigits : Nat := 1024
  deriving Repr

private abbrev Decoder := StateT (Array String × Nat) (Except String)
private def line : Decoder String := do
  let (lines,position) ← get
  match lines[position]? with
  | none => throw "truncated certificate"
  | some s => set (lines,position+1); return s
private def number (cap : Nat) : Decoder Nat := do
  let s ← line
  match s.toNat? with
  | some n =>
    if n > cap then throw "resource limit: count"
    if s != toString n then throw "noncanonical integer"
    return n
  | none => throw "invalid integer"
private def sourceId : Decoder Nat := do
  let n ← number (2^64-1)
  return if n=0 then 2^64-1 else n-1
private def flag : Decoder Bool := do return (← number 1) = 1
private def hexadecimal (s : String) (cap : Nat) : Except String Int := do
  let negative := s.startsWith "-"
  let digits := if negative then (s.drop 1).toString else s
  if digits.isEmpty then throw "empty integer"
  if digits.length > cap then throw "resource limit: integer growth"
  let mut value := 0
  for ch in digits.toList do
    let d := ch.toNat
    if d ≥ 48 && d ≤ 57 then value := value*16+(d-48)
    else if d ≥ 97 && d ≤ 102 then value := value*16+(d-87)
    else throw "invalid hexadecimal integer"
  if value = 0 then
    if s != "0" then throw "noncanonical zero"
  else
    if digits.length % 8 != 0 then throw "noncanonical limb width"
    if value < 16^(digits.length-8) then throw "leading zero limb"
  return if negative then -(value : Int) else (value : Int)
private def rational (limits : DecodeLimits) : Decoder Rat := do
  let s ← line
  match s.splitOn "/" with
  | [ns,ds] =>
    let n ← match hexadecimal ns limits.maxHexDigits with
      | .ok n => pure n | .error e => throw e
    let d ← match hexadecimal ds limits.maxHexDigits with
      | .ok d => pure d | .error e => throw e
    if d ≤ 0 then throw "nonpositive denominator"
    let q : Rat := (n : Rat)/(d : Rat)
    if q.num != n || q.den != d.toNat then throw "unnormalized rational"
    return q
  | _ => throw "invalid rational"
private def repeated (n : Nat) (p : Decoder α) : Decoder (Array α) := do
  let mut out := #[]
  for _ in [:n] do out := out.push (← p)
  return out
private def mesh (limits : DecodeLimits) : Decoder ExactMesh := do
  let nv ← number limits.maxVertices
  let nf ← number limits.maxFaces
  let ne ← number (nv+3*nf)
  let axis ← number 2
  let u ← number 2
  let w ← number 2
  let orientation ← flag
  let planar ← flag
  let mut points := #[]
  let mut sources := #[]
  let mut pinned := #[]
  for _ in [:nv] do
    sources := sources.push (← sourceId)
    pinned := pinned.push (← flag)
    points := points.push ⟨← rational limits,← rational limits,← rational limits⟩
  let faces ← repeated nf do return Face.mk (← number (nv-1)) (← number (nv-1)) (← number (nv-1))
  let constraints ← repeated ne do
    let a ← number (nv-1); let b ← number (nv-1); let kind ← number 2; let source ← sourceId
    return {a,b,kind,source : Constraint}
  return {points,sources,pinned,faces,constraints,axis,u,w,orientation,planar}
private def artifact (limits : DecodeLimits) : Decoder Certificate := do
  if (← line) != "TESS1" then throw "unsupported certificate version"
  if (← line) != "SEED-VISIBILITY-ROTATION-LEFT1-LAWSON1" then throw "unsupported seed policy"
  let axis ← number 3
  let strict ← flag
  let nr ← number (limits.maxVertices/3)
  let rings ← repeated (nr+1) (number limits.maxVertices)
  let seed ← mesh limits
  let output ← mesh limits
  if (← line) != "END" then throw "missing end marker"
  let (lines,position) ← get
  if position+1 != lines.size || lines[position]? != some "" then throw "trailing certificate data"
  return ⟨axis,strict,rings,seed,output⟩

def decodeCertificate (text : String) (limits : DecodeLimits := {}) : Except String Certificate := do
  if text.utf8ByteSize > limits.maxBytes then throw "resource limit: certificate bytes"
  let (cert,_) ← (artifact limits).run ((text.splitOn "\n").toArray,0)
  return cert

private def hexWord : Decoder Nat := do
  let text ← line
  if text.length != 16 then throw "invalid uint64 word"
  let mut value := 0
  for ch in text.toList do
    let d := ch.toNat
    if d≥48 && d≤57 then value:=value*16+(d-48)
    else if d≥97 && d≤102 then value:=value*16+(d-87)
    else throw "invalid uint64 word"
  return value
private def mesh2 (limits : DecodeLimits) : Decoder ExactMesh := do
  let nv ← number limits.maxVertices
  let nf ← number limits.maxFaces
  let ne ← number (nv+3*nf)
  let axis ← number 2; let u ← number 2; let w ← number 2
  let orientation ← flag; let planar ← flag
  let mut points := #[]; let mut sources := #[]; let mut pinned := #[]; let mut ids := #[]
  for _ in [:nv] do
    sources:=sources.push (← sourceId)
    pinned:=pinned.push (← flag)
    ids:=ids.push (← number (2^64-2))
    points:=points.push ⟨← rational limits,← rational limits,← rational limits⟩
  let mut faces := #[]; let mut faceIds := #[]
  for _ in [:nf] do
    faces:=faces.push ⟨← number (nv-1),← number (nv-1),← number (nv-1)⟩
    faceIds:=faceIds.push (← number (2^64-2))
  let constraints ← repeated ne do
    let a ← number (nv-1); let b ← number (nv-1); let kind ← number 3
    let source ← sourceId; let owner ← number (2^64-1)
    let ta ← rational limits; let tb ← rational limits; let tag ← hexWord
    return {a,b,kind,source,owner,ta,tb,tag : Constraint}
  return {points,sources,pinned,faces,constraints,axis,u,w,orientation,planar,vertexIds:=ids,faceIds}
private def artifact2 (limits : DecodeLimits) : Decoder Certificate2 := do
  if (← line)!="TESS2" then throw "unsupported certificate version"
  if (← line)!="SEED-VISIBILITY-ROTATION-LEFT1-LAWSON1" then throw "unsupported seed policy"
  let axis ← number 3; let strict ← flag; let nr ← number (limits.maxVertices/3)
  let rings ← repeated (nr+1) (number limits.maxVertices)
  if (← line)!="RUN2" then throw "missing run request"
  let targetCount ← number (2^64-1)
  let targetArea ← rational limits; let tolerance ← rational limits
  let subdivideBoundary ← flag; let subdivideFeatures ← flag; let ownerListMode ← flag
  let no ← number limits.maxVertices
  let owners ← repeated no (number (2^64-1))
  let qualityBits ← repeated 3 hexWord
  let maxPasses ← number (2^64-1); let maxEdits ← number (2^64-1); let maxCandidates ← number (2^64-1)
  let resourceCaps ← repeated 5 (number (2^64-1))
  let seed ← mesh2 limits; let output ← mesh2 limits
  if (← line)!="END" then throw "missing end marker"
  let (lines,position) ← get
  if position+1!=lines.size || lines[position]?!=some "" then throw "trailing certificate data"
  return ⟨⟨axis,strict,rings,seed,output⟩,⟨targetCount,targetArea,tolerance,subdivideBoundary,subdivideFeatures,ownerListMode,
    owners,qualityBits,maxPasses,maxEdits,maxCandidates,resourceCaps⟩⟩

def decodeCertificate2 (text : String) (limits : DecodeLimits := {}) : Except String Certificate2 := do
  if text.utf8ByteSize>limits.maxBytes then throw "resource limit: certificate bytes"
  let (cert,_) ← (artifact2 limits).run ((text.splitOn "\n").toArray,0)
  return cert
end Tess
