import TobjSubd

/-! `subdobj FILE.obj` — reference implementation used for the C differential.
Prints `mesh <i> ok=<0|1>` per mesh followed by its canonical tag lines.

`subdobj --roundtrip FILE...` checks, for every accepted mesh, that parsing the
canonical lines gives back the same model. -/
open TobjSubd

/-- Number of accepted meshes, or `none` if one does not round-trip. -/
def roundtrip (text : S) : Option Nat :=
  (parseObj text).foldlM (fun n m =>
    let t : Topo := ⟨m.faces⟩
    let s := parseLines t m.lines
    if !ok s then some n
    else if parseLines t (splitOn '\n' (print s)) == s then some (n + 1) else none) 0

def main (args : List String) : IO UInt32 := do
  match args with
  | "--roundtrip" :: paths =>
    let mut total := 0
    for p in paths do
      match roundtrip (← IO.FS.readFile p).toList with
      | some n => total := total + n
      | none => IO.eprintln s!"round-trip MISMATCH: {p}"; return 1
    IO.println s!"subd round-trip: {total} accepted meshes ok"
    pure 0
  | [path] =>
    IO.print (String.ofList (dumpObj (← IO.FS.readFile path).toList))
    pure 0
  | _ =>
    IO.eprintln "usage: subdobj FILE.obj | subdobj --roundtrip FILE..."
    pure 2
