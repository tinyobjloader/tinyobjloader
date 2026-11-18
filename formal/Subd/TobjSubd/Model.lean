/-!
# Subdivision-surface tags in .obj: normative model

Executable specification of `subd-obj.md`. `tobj_subd.c` mirrors each definition
(comments there name the Lean function).

* `lineTokens` / `dropCR`: blank-separated tokens of a line.
* `parseInt?`, `isDecimal`, `parseCounts?`: the number grammars.
* `step`: one `t` line applied to the model; any rule violation sets `bad`.
* `parseLines`: all lines of a mesh, then the whole-mesh rules (`finish`).
* `print`: canonical form (only for accepted models).
-/
namespace TobjSubd

abbrev S := List Char

def isBlank (c : Char) : Bool := c == ' ' || c == '\t'
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- Split at every blank (empty pieces included). -/
def splitBlank : S → List S
  | [] => [[]]
  | c :: cs =>
    if isBlank c then [] :: splitBlank cs
    else match splitBlank cs with
      | [] => [[c]]
      | w :: ws => (c :: w) :: ws

/-- Maximal runs of non-blank characters. -/
def lineTokens (cs : S) : List S := (splitBlank cs).filter (!·.isEmpty)

/-- Drop one trailing carriage return. -/
def dropCR (cs : S) : S :=
  if cs.getLast? == some '\r' then cs.dropLast else cs

/-! ## Numbers -/

def digitsVal (ds : S) : Nat := ds.foldl (fun v d => v * 10 + (d.toNat - '0'.toNat)) 0

/-- `[+-]?[0-9]+` -/
def parseInt? (s : S) : Option Int :=
  let (neg, ds) := match s with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  if ds.isEmpty || !ds.all isDigit then none
  else let v : Int := digitsVal ds; some (if neg then -v else v)

def isDecChar (c : Char) : Bool := isDigit c || c == '.' || c == 'e' || c == 'E' || c == '+' || c == '-'

/-- `[+-]?([0-9]+(\.[0-9]*)?|\.[0-9]+)([eE][+-]?[0-9]+)?` (the first two conjuncts are implied by
the grammar; they are stated so that proofs can use them directly). -/
def isDecimalCore (s : S) : Bool :=
  let s := match s with | '+' :: r => r | '-' :: r => r | r => r
  let ip := s.takeWhile isDigit
  let r := s.dropWhile isDigit
  let (fp, r) := match r with
    | '.' :: r' => (r'.takeWhile isDigit, r'.dropWhile isDigit)
    | _ => ([], r)
  if ip.length + fp.length == 0 then false
  else match r with
    | [] => true
    | e :: r' =>
      if e == 'e' || e == 'E' then
        let r' := match r' with | '+' :: x => x | '-' :: x => x | x => x
        !r'.isEmpty && r'.all isDigit
      else false

def isDecimal (s : S) : Bool := !s.isEmpty && s.all isDecChar && isDecimalCore s


def maxCount : Nat := 8192

def splitOn (sep : Char) : S → List S
  | [] => [[]]
  | c :: cs =>
    if c == sep then [] :: splitOn sep cs
    else match splitOn sep cs with
      | [] => [[c]]
      | w :: ws => (c :: w) :: ws

def count? (s : S) : Option Nat :=
  if s.isEmpty || !s.all isDigit then none
  else let v := digitsVal s; if v ≤ maxCount then some v else none

/-- `ni/nf/ns`, each `[0-9]+` and at most `maxCount`. -/
def parseCounts? (s : S) : Option (Nat × Nat × Nat) :=
  match splitOn '/' s with
  | [a, b, c] => do pure (← count? a, ← count? b, ← count? c)
  | _ => none

/-! ## Mesh topology -/

structure Topo where
  faces : List (List Nat)

def faceEdges (f : List Nat) : List (Nat × Nat) :=
  (f.zip (f.drop 1 ++ f.take 1)).map fun (a, b) => (min a b, max a b)

def Topo.hasEdge (t : Topo) (a b : Nat) : Bool := (t.faces.flatMap faceEdges).contains (a, b)
def Topo.hasVert (t : Topo) (v : Nat) : Bool := t.faces.any (·.contains v)
def Topo.numFaces (t : Topo) : Nat := t.faces.length
def Topo.allTris (t : Topo) : Bool := t.faces.all (·.length == 3)

/-! ## Model -/

structure Subd where
  scheme : Option Nat := none     -- 0 catmark, 1 loop, 2 bilinear
  ib : Option Nat := none         -- interpolateboundary 0..2
  fvar : Option Nat := none       -- facevaryinginterpolateboundary 0..5
  cm : Option Nat := none         -- creasemethod: 0 normal, 1 chaikin
  st : Option Nat := none         -- smoothtriangles: 0 catmark, 1 smooth
  creases : List ((Nat × Nat) × S) := []
  corners : List (Nat × S) := []
  holes : List Nat := []
  unknown : List S := []
  bad : Bool := false
  deriving Repr, DecidableEq

def Subd.err (s : Subd) : Subd := { s with bad := true }

/-- Negative sharpness counts as `0`. -/
def sharp (t : S) : S := if t.head? == some '-' then ['0'] else t

/-- Set the value of key `k`: replace in place, or append. -/
def upsert {κ : Type} [BEq κ] (k : κ) (v : S) : List (κ × S) → List (κ × S)
  | [] => [(k, v)]
  | (k', v') :: r => if k' == k then (k, v) :: r else (k', v') :: upsert k v r

def Subd.setCrease (s : Subd) (a b : Nat) (v : S) : Subd :=
  { s with creases := upsert (a, b) (sharp v) s.creases }

def Subd.setCorner (s : Subd) (v : Nat) (x : S) : Subd :=
  { s with corners := upsert v (sharp x) s.corners }

def Subd.addHole (s : Subd) (f : Nat) : Subd :=
  if s.holes.contains f then s else { s with holes := s.holes ++ [f] }

/-- Set a scalar slot; repeating a scalar tag is an error. -/
def setScalar (s : Subd) (slot : Option Nat) (v : Nat) (upd : Subd → Nat → Subd) : Subd :=
  if slot.isSome then s.err else upd s v

def pairs : List Int → List (Int × Int)
  | a :: b :: r => (a, b) :: pairs r
  | _ => []

def stepCrease (t : Topo) (s : Subd) (ps : List (Int × Int)) (vals : List S) (shared : Bool) :
    Subd :=
  (ps.zipIdx).foldl (fun s ((x, y), k) =>
    if x < 0 || y < 0 || x == y then s.err
    else
      let lo := (min x y).toNat; let hi := (max x y).toNat
      if !t.hasEdge lo hi then s.err
      else s.setCrease lo hi (vals.getD (if shared then 0 else k) ['0'])) s

def stepCorner (t : Topo) (s : Subd) (vs : List Int) (vals : List S) (shared : Bool) : Subd :=
  (vs.zipIdx).foldl (fun s (x, k) =>
    if x < 0 || !t.hasVert x.toNat then s.err
    else s.setCorner x.toNat (vals.getD (if shared then 0 else k) ['0'])) s

def holeStep (t : Topo) (s : Subd) (x : Int) : Subd :=
  if x < 0 || x.toNat ≥ t.numFaces then s.err else s.addHole x.toNat

def stepHole (t : Topo) (s : Subd) (vs : List Int) : Subd := vs.foldl (holeStep t) s

def lookup (v : S) (names : List String) : Option Nat :=
  (names.zipIdx.find? fun (n, _) => n.toList == v).map (·.2)

def joinSp : List S → S
  | [] => []
  | [w] => w
  | w :: ws => w ++ ' ' :: joinSp ws

/-- `interpolateboundary` (`fv = false`, values 0..2) or
`facevaryinginterpolateboundary` (`fv = true`, values 0..5). -/
def stepBoundary (s : Subd) (fv : Bool) (x : Int) : Subd :=
  if x < 0 || x > (if fv then 5 else 2) then s.err
  else if fv then setScalar s s.fvar x.toNat fun s v => { s with fvar := some v }
  else setScalar s s.ib x.toNat fun s v => { s with ib := some v }

/-- `scheme` (0), `creasemethod` (1) or `smoothtriangles` (2) with string value `v`. -/
def stepName (s : Subd) (which : Nat) (v : S) : Subd :=
  match which with
  | 0 => match lookup v ["catmark", "loop", "bilinear"] with
    | none => s.err
    | some x => setScalar s s.scheme x fun s v => { s with scheme := some v }
  | 1 => match lookup v ["normal", "chaikin"] with
    | none => s.err
    | some x => setScalar s s.cm x fun s v => { s with cm := some v }
  | _ => match lookup v ["catmark", "smooth"] with
    | none => s.err
    | some x => setScalar s s.st x fun s v => { s with st := some v }

/-- A tag with well-formed counts and arguments. -/
def stepTag (t : Topo) (s : Subd) (args : List S) (n : String) (ni nf ns : Nat)
    (ints : List Int) (flts strs : List S) : Subd :=
  if n == "crease" then
    if ni ≥ 2 && ni % 2 == 0 && ns == 0 && (nf == 1 || nf == ni / 2) then
      stepCrease t s (pairs ints) flts (nf == 1)
    else s.err
  else if n == "corner" then
    if ni ≥ 1 && ns == 0 && (nf == 1 || nf == ni) then stepCorner t s ints flts (nf == 1)
    else s.err
  else if n == "hole" then
    if ni ≥ 1 && nf == 0 && ns == 0 then stepHole t s ints else s.err
  else if n == "interpolateboundary" || n == "facevaryinginterpolateboundary" then
    if ni == 1 && nf == 0 && ns == 0 then
      stepBoundary s (n == "facevaryinginterpolateboundary") (ints.headD 0)
    else s.err
  else if n == "facevaryingpropagatecorners" then
    if ni == 1 && nf == 0 && ns == 0 then s else s.err
  else if n == "scheme" || n == "creasemethod" || n == "smoothtriangles" then
    if ni == 0 && nf == 0 && ns == 1 then
      stepName s (if n == "scheme" then 0 else if n == "creasemethod" then 1 else 2) (strs.headD [])
    else s.err
  else { s with unknown := s.unknown ++ [joinSp (['t'] :: args)] }

/-- A parsed tag line: name, counts, integers, decimals, strings. -/
structure Tag where
  name : String
  ni : Nat
  nf : Nat
  ns : Nat
  ints : List Int
  flts : List S
  strs : List S

/-- The state-free part of a `t` line: counts and argument kinds. -/
def classify (args : List S) : Option Tag :=
  match args with
  | name :: cnt :: rest =>
    match parseCounts? cnt with
    | none => none
    | some (ni, nf, ns) =>
      if rest.length != ni + nf + ns then none else
      match (rest.take ni).mapM parseInt? with
      | none => none
      | some ints =>
        if !((rest.drop ni).take nf).all isDecimal then none
        else some ⟨String.ofList name, ni, nf, ns, ints, (rest.drop ni).take nf, rest.drop (ni + nf)⟩
  | _ => none

/-- One `t` line, given its tokens after `t`. -/
def step (t : Topo) (s : Subd) (args : List S) : Subd :=
  match classify args with
  | none => s.err
  | some g => stepTag t s args g.name g.ni g.nf g.ns g.ints g.flts g.strs

/-- Whole-mesh rules, after all tag lines. -/
def finish (t : Topo) (s : Subd) : Subd :=
  let s := if s.st.isSome && s.scheme.isSome && s.scheme != some 0 then s.err else s
  if s.scheme == some 1 && !t.allTris then s.err else s

/-- Parse and check a mesh's lines (lines whose first token is not `t` are ignored). -/
def parseLines (t : Topo) (lines : List S) : Subd :=
  finish t (lines.foldl (fun s l =>
    match lineTokens (dropCR l) with
    | ['t'] :: args => step t s args
    | _ => s) {})

def ok (s : Subd) : Bool := !s.bad

/-! ## Canonical form -/

def digitChar (k : Nat) : Char := Char.ofNat (48 + k)

/-- Decimal digits of `n` (same as `toString n`). -/
def nat (n : Nat) : S :=
  if n < 10 then [digitChar n] else nat (n / 10) ++ [digitChar (n % 10)]
decreasing_by omega

def chunks (k : Nat) (l : List Nat) : List (List Nat) :=
  if k = 0 then [l] else
  let rec go (fuel : Nat) (l : List Nat) : List (List Nat) :=
    match fuel, l with
    | 0, _ => []
    | _, [] => []
    | fuel + 1, l => l.take k :: go fuel (l.drop k)
  go l.length l

def line (ws : List S) : S := joinSp ws ++ ['\n']

def scalLine (tag : String) (cnt : String) (v : Option S) : List S :=
  match v with | some x => [joinSp ["t".toList, tag.toList, cnt.toList, x]] | none => []

def nameOf (ns : List String) (v : Option Nat) : Option S := v.map fun i => (ns.getD i "").toList

def creaseLine (c : (Nat × Nat) × S) : S :=
  joinSp ["t".toList, "crease".toList, "2/1/0".toList, nat c.1.1, nat c.1.2, c.2]

def cornerLine (c : Nat × S) : S := joinSp ["t".toList, "corner".toList, "1/1/0".toList, nat c.1, c.2]

def holeLine (hs : List Nat) : S :=
  joinSp (["t".toList, "hole".toList, nat hs.length ++ "/0/0".toList] ++ hs.map nat)

def scalarLines (s : Subd) : List S :=
  scalLine "scheme" "0/0/1" (nameOf ["catmark", "loop", "bilinear"] s.scheme) ++
  scalLine "interpolateboundary" "1/0/0" (s.ib.map nat) ++
  scalLine "facevaryinginterpolateboundary" "1/0/0" (s.fvar.map nat) ++
  scalLine "creasemethod" "0/0/1" (nameOf ["normal", "chaikin"] s.cm) ++
  scalLine "smoothtriangles" "0/0/1" (nameOf ["catmark", "smooth"] s.st)

/-- Canonical lines, without line ends. -/
def printLines (s : Subd) : List S :=
  scalarLines s ++ s.creases.map creaseLine ++ s.corners.map cornerLine ++
    (chunks maxCount s.holes).map holeLine ++ s.unknown

def print (s : Subd) : S := if s.bad then [] else (printLines s).flatMap (· ++ ['\n'])

/-! ## `.obj` subset for differential testing (`tobj_subd_dump_obj`) -/

structure OMesh where
  lines : List S := []
  faces : List (List Nat) := []

/-- Face vertex: the integer before the first `/`, 1-based or negative-relative. -/
def faceVertex (nverts : Nat) (tok : S) : Option Nat := do
  let v ← parseInt? (tok.takeWhile (· != '/'))
  let idx : Int := if v > 0 then v - 1 else nverts + v
  if v == 0 || idx < 0 || idx ≥ nverts then none else some idx.toNat

def parseObj (text : S) : List OMesh :=
  let (ms, _) := (splitOn '\n' text).foldl (fun (acc : List OMesh × Nat) raw =>
    let (ms, nv) := acc
    let l := dropCR raw
    let cur := ms.getLastD {}
    let set (m : OMesh) := ms.dropLast ++ [m]
    match lineTokens l with
    | ['v'] :: _ => (ms, nv + 1)
    | ['o'] :: _ => (ms ++ [{}], nv)
    | ['g'] :: _ => (ms ++ [{}], nv)
    | ['t'] :: _ => (set { cur with lines := cur.lines ++ [l] }, nv)
    | ['f'] :: vs =>
      if vs.length ≥ 3 then
        match vs.mapM (faceVertex nv) with
        | some f => (set { cur with faces := cur.faces ++ [f] }, nv)
        | none => (ms, nv)
      else (ms, nv)
    | _ => (ms, nv)) ([{}], 0)
  ms

def dumpObj (text : S) : S :=
  (parseObj text).zipIdx.flatMap fun (m, i) =>
    if m.faces.isEmpty && m.lines.isEmpty then [] else
    let s := parseLines ⟨m.faces⟩ m.lines
    "mesh ".toList ++ nat i ++ (if ok s then " ok=1\n" else " ok=0\n").toList ++ print s

end TobjSubd
