import TobjSkel

/-! `skelobj FILE.obj` — reference implementation used for the C differential.

`skelobj --roundtrip FILE...` checks that parsing the canonical lines of an
accepted skeleton gives back the same model. -/
open TobjSkel TobjSubd

def maxVw (text : S) : Int :=
  (splitOn '\n' text).foldl (fun m l => match lineTokens (dropCR l) with
    | ['v', 'w'] :: _ :: ids => (jointIds ids).foldl max m
    | _ => m) (-1 : Int)

def main (args : List String) : IO UInt32 := do
  match args with
  | "--roundtrip" :: paths =>
    let mut n := 0
    for p in paths do
      let text := (← IO.FS.readFile p).toList
      let skel := (splitOn '\n' text).filter fun l => match lineTokens (dropCR l) with
        | kw :: _ => isSkelKw kw
        | [] => false
      let s := parseLines skel (maxVw text)
      if ok s then
        if parseLines (printLines s) (maxVw text) == s then n := n + 1
        else IO.eprintln s!"round-trip MISMATCH: {p}"; return 1
    IO.println s!"skel round-trip: {n} accepted skeletons ok"
    pure 0
  | [path] =>
    IO.print (String.ofList (TobjSkel.dumpObj (← IO.FS.readFile path).toList))
    pure 0
  | _ =>
    IO.eprintln "usage: skelobj FILE.obj | skelobj --roundtrip FILE..."
    pure 2
