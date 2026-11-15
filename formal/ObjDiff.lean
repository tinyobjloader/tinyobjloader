/-
  Differential-testing driver: run the pure Lean parse model (`Obj.parseObj`,
  Obj/Mesh.lean) on an `.obj` file without triangulation and print a canonical
  topology dump.  `tests/obj_dump.c` prints the same dump from the C loader;
  `tools/objdiff.sh` diffs the two over a set of models.

  Usage: objdiff FILE.obj
-/
import Obj
open Obj

def showIdx (i : Idx) : String :=
  s!"{i.v}/{i.t}/{i.n}"

def bytesToString (bs : List Nat) : String := String.mk (bs.map Char.ofNat)

def dumpShape (s : Shape) : String :=
  let faces := faceList s.idx s.fv
  let lines := faces.map fun f => " f " ++ " ".intercalate (f.map showIdx)
  let sgs := " sg " ++ " ".intercalate (s.sg.map toString)
  "shape " ++ bytesToString s.name ++ "\n" ++ "\n".intercalate lines ++
    (if lines.isEmpty then "" else "\n") ++ sgs ++ "\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let data ← IO.FS.readBinFile path
    let bytes := data.toList.map UInt8.toNat
    let shapes := parseObj (fun cs => fanTris cs.length) [] false bytes
    IO.print ("".intercalate (shapes.map dumpShape))
    return 0
  | _ =>
    IO.eprintln "usage: objdiff FILE.obj"
    return 2
