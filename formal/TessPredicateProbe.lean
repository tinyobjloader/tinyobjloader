import Tess.PredicateFixture

private def readBounded : IO String := do
  let input ← IO.getStdin
  let mut bytes := ByteArray.empty
  let limit := 8388608
  for _ in [:limit/65536+2] do
    let chunk ← input.read 65536
    if bytes.size+chunk.size>limit then throw (IO.userError "resource limit: input bytes")
    if chunk.size=0 then
      match String.fromUTF8? bytes with
      | some text => return text
      | none => throw (IO.userError "invalid UTF-8")
    bytes:=bytes++chunk
  throw (IO.userError "resource limit: input bytes")

def main (args : List String) : IO UInt32 := do
  if !args.isEmpty then
    IO.eprintln "usage: tesspredicates < exact-rational-fixtures.txt"
    return 2
  try
    let text ← readBounded
    let newlineCount:=text.foldl (fun count ch => if ch='\n' then count+1 else count) 0
    if newlineCount>20000 then
      IO.eprintln "resource limit: fixture count"
      return 3
    let lines := (text.splitOn "\n").filter (fun line => !line.isEmpty)
    if lines.length>20000 then
      IO.eprintln "resource limit: fixture count"
      return 3
    for line in lines do
      match Tess.PredicateFixture.decodeLine line with
      | .ok value => IO.println value
      | .error message =>
        IO.eprintln message
        return if message.startsWith "resource limit" then 3 else 1
    return 0
  catch error =>
    let message:=error.toString
    IO.eprintln message
    return if (message.splitOn "resource limit").length>1 then 3 else 1
