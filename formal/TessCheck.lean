import Tess.V2Check

private def boundedHandle (read : USize → IO ByteArray) (limit : Nat) : IO String := do
  let mut bytes := ByteArray.empty
  let mut remaining := limit
  let mut done := false
  for _ in [:limit/65536+2] do
    if !done then
      let chunk ← read ((min 65536 (remaining+1)).toUSize)
      if chunk.size=0 then done := true
      else
        if chunk.size > remaining then throw (IO.userError "resource limit: certificate bytes")
        bytes := bytes ++ chunk
        remaining := remaining-chunk.size
  if !done then throw (IO.userError "resource limit: certificate bytes")
  match String.fromUTF8? bytes with
  | some text => return text
  | none => return "" -- cannot decode as either accepted certificate version

private def boundedRead (path : System.FilePath) (limit : Nat) : IO String := do
  let handle ← IO.FS.Handle.mk path .read
  boundedHandle handle.read limit

private def checkPair (requestText certText : String) : IO UInt32 := do
  let limits : Tess.DecodeLimits := {}
  if requestText.startsWith "TESS2\n" && certText.startsWith "TESS2\n" then
    match Tess.decodeCertificate2 requestText limits,Tess.decodeCertificate2 certText limits with
    | .ok request,.ok cert =>
      let seed:=cert.snapshot.seed.faces.size; let output:=cert.snapshot.output.faces.size
      if seed^2+output^2+seed*output>1000000 then
        IO.eprintln "resource limit: validation work"; return 3
      if Tess.check2 request cert then
        IO.println "accepted: version-2 graph, domain, constraints and height bound"
        return 0
      IO.eprintln "certificate rejected"; return 1
    | .error error,_ | _,.error error =>
      IO.eprintln error; return if error.startsWith "resource limit" then 3 else 1
  else
    match Tess.decodeCertificate requestText limits,Tess.decodeCertificate certText limits with
    | .ok request,.ok cert =>
      let seed:=cert.seed.faces.size; let output:=cert.output.faces.size
      if seed^2+output^2+seed*output>1000000 then
        IO.eprintln "resource limit: validation work"; return 3
      if Tess.check request cert then
        IO.println "accepted: version-1 fixed-boundary exact graph certificate"
        return 0
      IO.eprintln "certificate rejected"; return 1
    | .error error,_ | _,.error error =>
      IO.eprintln error; return if error.startsWith "resource limit" then 3 else 1

def main (args : List String) : IO UInt32 := do
  try
    let limits : Tess.DecodeLimits := {}
    match args with
    | ["--stdin"] =>
      let text ← boundedHandle (← IO.getStdin).read (2*limits.maxBytes+1)
      match text.splitOn (String.singleton (Char.ofNat 0)) with
      | [request,result] => checkPair request result
      | _ => IO.eprintln "expected request NUL result"; return 1
    | [requestPath,resultPath] =>
      checkPair (← boundedRead requestPath limits.maxBytes) (← boundedRead resultPath limits.maxBytes)
    | _ =>
      IO.eprintln "usage: tesscheck caller-held-request.tess result.tess | --stdin"
      return 2
  catch error =>
    IO.eprintln error.toString
    return 3
