import TobjSubd.Model

/-!
# Skeletons in .obj: normative model

Executable specification of `skel-obj.md`; `tobj_skel.c` mirrors it. Tokens and
the decimal grammar are those of `TobjSubd` (subd-obj.md).

* `step`: one `skel_*` line; any rule violation sets `bad`.
* `parseLines`: all lines, then the whole-file rules (`finish`).
* `printLines` / `print`: canonical form.
-/
namespace TobjSkel
open TobjSubd

def isAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- `[A-Za-z_][A-Za-z0-9_]*` -/
def validName : S → Bool
  | [] => false
  | c :: r => (isAlpha c || c == '_') && r.all fun c => isAlpha c || isDigit c || c == '_'

structure Joint where
  name : S
  parent : Option Nat := none   -- index of an earlier joint
  bind : Option (List S) := none  -- 16 decimals
  rest : Option (List S) := none  -- 16 decimals
  deriving Repr, DecidableEq

structure Skel where
  joints : List Joint := []
  lib : Option (S × Option S) := none
  anim : Option (S × Option S) := none
  ext : Bool := false
  bad : Bool := false
  deriving Repr, DecidableEq

def Skel.err (s : Skel) : Skel := { s with bad := true }

def findJoint (js : List Joint) (n : S) : Option Nat := js.findIdx? (·.name == n)

def isMatrix (m : List S) : Bool := m.length == 16 && m.all isDecimal

def kwJoint : S := "skel_joint".toList
def kwRest : S := "skel_rest".toList
def kwLib : S := "skel_lib".toList
def kwAnim : S := "skel_anim".toList

def isSkelKw (k : S) : Bool := k == kwJoint || k == kwRest || k == kwLib || k == kwAnim

/-- Replace the element at `i`. -/
def setAt {α : Type} (l : List α) (i : Nat) (x : α) : List α := l.set i x

/-- `-` (a root), or the index of an earlier joint named `par`. -/
def parentOf? (js : List Joint) (par : S) : Option (Option Nat) :=
  if par == ['-'] then some none else (findJoint js par).map some

def bindOf (m : List S) : Option (List S) := if m.isEmpty then none else some m

def Skel.addJoint (s : Skel) (j : Joint) : Skel := { s with joints := s.joints ++ [j] }

def stepJoint (s : Skel) (args : List S) : Skel :=
  match args with
  | name :: par :: m =>
    if !(m.length == 0 || m.length == 16) then s.err
    else if !validName name then s.err
    else if (findJoint s.joints name).isSome then s.err
    else
      match parentOf? s.joints par with
      | none => s.err
      | some p =>
        if m.length == 16 && !m.all isDecimal then s.err
        else s.addJoint ⟨name, p, bindOf m, none⟩
  | _ => s.err

def stepRest (s : Skel) (args : List S) : Skel :=
  match args with
  | name :: m =>
    if m.length != 16 then s.err else
    match findJoint s.joints name with
    | none => s.err
    | some i =>
      match s.joints[i]? with
      | none => s.err
      | some j =>
        if j.rest.isSome then s.err
        else if !m.all isDecimal then s.err
        else { s with joints := setAt s.joints i { j with rest := some m } }
  | [] => s.err

def stepSlot (s : Skel) (lib : Bool) (args : List S) : Skel :=
  let slot := if lib then s.lib else s.anim
  let set (v : Option (S × Option S)) := if lib then { s with lib := v } else { s with anim := v }
  match args with
  | [p] => if slot.isSome then s.err else set (some (p, none))
  | [p, n] => if slot.isSome then s.err else set (some (p, some n))
  | _ => s.err

def step (s : Skel) (kw : S) (args : List S) : Skel :=
  if kw == kwJoint then stepJoint s args
  else if kw == kwRest then stepRest s args
  else stepSlot s (kw == kwLib) args

def lineStep (s : Skel) (l : S) : Skel :=
  match lineTokens (dropCR l) with
  | kw :: args => if isSkelKw kw then step { s with ext := true } kw args else s
  | [] => s

/-- Whole-file rules. `maxId` is the largest `vw` joint id, or `-1`. -/
def finish (maxId : Int) (s : Skel) : Skel :=
  if !s.ext then s else
  let s := if s.joints.any (·.bind.isNone) && s.lib.isNone then s.err else s
  if maxId ≥ 0 && maxId ≥ s.joints.length then s.err else s

def parseLines (lines : List S) (maxId : Int) : Skel :=
  finish maxId (lines.foldl lineStep {})

def ok (s : Skel) : Bool := s.ext && !s.bad

/-! ## Canonical form -/

def parentName (js : List Joint) (p : Option Nat) : S :=
  match p with
  | none => ['-']
  | some i => ((js[i]?).map (·.name)).getD ['-']

def jointLine (js : List Joint) (j : Joint) : S :=
  joinSp ([kwJoint, j.name, parentName js j.parent] ++ j.bind.getD [])

def restLine (j : Joint) (m : List S) : S := joinSp ([kwRest, j.name] ++ m)

def slotLine (kw : S) : Option (S × Option S) → List S
  | none => []
  | some (p, n) => [joinSp ([kw, p] ++ n.toList)]

def printLines (s : Skel) : List S :=
  s.joints.map (jointLine s.joints) ++
  (s.joints.filterMap fun j => j.rest.map (restLine j)) ++
  slotLine kwLib s.lib ++ slotLine kwAnim s.anim

def print (s : Skel) : S := if ok s then (printLines s).flatMap (· ++ ['\n']) else []

/-! ## `.obj` subset for differential testing (`tobj_skel_dump_obj`) -/

/-- Joint ids of a `vw` line after `<vertex>`: `(<joint> <weight>)*`. -/
def jointIds : List S → List Int
  | j :: _ :: r => (parseInt? j).toList ++ jointIds r
  | [j] => (parseInt? j).toList
  | [] => []

def dumpObj (text : S) : S :=
  let lines := splitOn '\n' text
  let skel := lines.filter fun l => match lineTokens (dropCR l) with
    | kw :: _ => isSkelKw kw
    | [] => false
  let maxId := lines.foldl (fun m l => match lineTokens (dropCR l) with
    | ['v', 'w'] :: _ :: ids => (jointIds ids).foldl max m
    | _ => m) (-1 : Int)
  let s := parseLines skel maxId
  if !s.ext then "skel none\n".toList
  else ("skel ok=" ++ (if ok s then "1" else "0") ++ " joints=").toList ++ nat s.joints.length ++
    ['\n'] ++ print s

end TobjSkel
