import TobjMtlx

/-! `mtlxmtl FILE.mtl` — reference implementation used for the C differential.
Prints one `mat <name> ext=<0|1> ok=<0|1>` line per material, then the MaterialX document. -/
open TobjMtlx MtlxSpec

def dump (text : String) : String :=
  let ms := parseMtl text.toList
  let hdr := String.join (ms.map fun m =>
    s!"mat {String.ofList m.name} ext={if m.ext then 1 else 0} ok={if m.ext && check m then 1 else 0}\n")
  hdr ++ printXml (toDoc ms)

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    IO.print (dump (← IO.FS.readFile path))
    pure 0
  | _ =>
    IO.eprintln "usage: mtlxmtl FILE.mtl"
    pure 2
