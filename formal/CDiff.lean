/-
  Differential-testing driver: runs the MiniC semantics of the translated
  C code (Obj.C.Gen) and the Lean specification (Obj.Glb) on inputs read
  from stdin, printing results in the same format as formal/tools/cdiff_c.c
  (which runs the real compiled C). formal/tools/cdiff.py compares them.

  Input lines:
    frame <hex bytes>
    layout <json_len> <bin_len> <is64>
-/
import Obj

open Obj Obj.C

def parseHex (s : String) : List UInt8 :=
  let cs := s.toList
  let rec go : List Char → List UInt8
    | a :: b :: rest =>
      let h (c : Char) : Nat :=
        if c.isDigit then c.toNat - '0'.toNat
        else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
        else c.toNat - 'A'.toNat + 10
      (h a * 16 + h b).toUInt8 :: go rest
    | _ => []
  go cs

def frameFields (blk : List UInt8) : List Nat :=
  let rd (o n : Nat) := decodeLE ((blk.drop o).take n)
  [rd 0 8, rd 8 8, rd 16 8, rd 24 8, rd 32 4, rd 36 4, rd 40 4]

def fuel : Nat := 100000

def showRes (r : Res (Option Val × Mem)) (frameBlk : Nat) : String :=
  match r with
  | .ok (some (.int _ n), m) =>
    match m frameBlk with
    | some blk => s!"{n} " ++ " ".intercalate ((frameFields blk).map toString)
    | none => "ERR"
  | .ok _ => "ERR noval"
  | .ub => "UB"
  | .timeout => "TIMEOUT"

def errCode : Glb.Err → Nat
  | .header => 22 | .magic => 20 | .version => 21 | .sizeMismatch => 24 | .chunk => 23

def specFrame (d : List UInt8) : String :=
  match Glb.parseFrame d with
  | .ok f => s!"0 {f.jsonOff} {f.jsonLen} {f.binOff} {f.binLen} {if f.hasJson then 1 else 0} " ++
             s!"{if f.hasBin then 1 else 0} {if f.is64 then 1 else 0}"
  | .error e => s!"{errCode e}"

def runLine (line : String) : String :=
  match line.trimAscii.toString.splitOn " " with
  | ["frame", hex] =>
    let d := parseHex hex
    let mem : Mem := fun b => if b = 0 then some d else if b = 1 then some (List.replicate 48 0) else none
    let r := callFunc Gen.prog fuel Gen.fid_tg3__glb_frame_parse
      [.ptr 0 0, .int IntTy.u64 d.length, .ptr 1 0] mem
    let c := showRes r 1
    -- On error the C frame contents are unspecified by the spec; print code only.
    let c := if c.startsWith "0 " then c else (c.splitOn " ").head!
    s!"{c} | {specFrame d}"
  | ["frame"] =>
    let d : List UInt8 := []
    let mem : Mem := fun b => if b = 0 then some d else if b = 1 then some (List.replicate 48 0) else none
    let r := callFunc Gen.prog fuel Gen.fid_tg3__glb_frame_parse
      [.ptr 0 0, .int IntTy.u64 0, .ptr 1 0] mem
    s!"{(showRes r 1).splitOn " " |>.head!} | {specFrame d}"
  | ["layout", jl, bl, is64] =>
    let jl := jl.toNat!
    let bl := bl.toNat!
    let is64 := is64.toNat!
    let mem : Mem := fun b => if b = 1 then some (List.replicate 48 0)
      else if b = 2 then some (List.replicate 8 0) else none
    let r := callFunc Gen.prog fuel Gen.fid_tg3__glb_layout
      [.int IntTy.u64 jl, .int IntTy.u64 bl, .int IntTy.i32 is64, .ptr 1 0, .ptr 2 0] mem
    let c := match r with
      | .ok (some (.int _ n), m) =>
        match m 1, m 2 with
        | some blk, some tot =>
          s!"{n} {decodeLE tot} " ++ " ".intercalate ((frameFields blk).map toString)
        | _, _ => "ERR"
      | .ub => "UB"
      | .timeout => "TIMEOUT"
      | _ => "ERR"
    let spec := match Glb.layout jl bl (is64 != 0) with
      | some (f, total) =>
        s!"1 {total} {f.jsonOff} {f.jsonLen} {f.binOff} {f.binLen} {if f.hasJson then 1 else 0} " ++
        s!"{if f.hasBin then 1 else 0} {if f.is64 then 1 else 0}"
      | none => "0"
    let c := if c.startsWith "1 " then c else (c.splitOn " ").head!
    s!"{c} | {spec}"
  | _ => "BADLINE"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let mut line ← stdin.getLine
  while line != "" do
    IO.println (runLine line)
    line ← stdin.getLine
