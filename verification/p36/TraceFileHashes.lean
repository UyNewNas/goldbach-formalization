import Lake.Build.Trace

/-- Read-only hashes with the exact Lake algorithm used by saved build traces.
Input records are `text<TAB>path` or `binary<TAB>path`; no file is modified. -/
def main (args : List String) : IO UInt32 := do
  let [request] := args | throw <| IO.userError "expected one request file"
  for line in (← IO.FS.readFile request).splitOn "\n" do
    if line.isEmpty then continue
    let [kind, path] := line.splitOn "\t" |
      throw <| IO.userError "invalid hash request record"
    unless kind == "text" || kind == "binary" do
      throw <| IO.userError "unknown hash request kind"
    let digest ← Lake.computeFileHash path (kind == "text")
    IO.println <| Lean.Json.compress <| Lean.Json.mkObj [
      ("path", Lean.toJson path), ("kind", Lean.toJson kind),
      ("hash", Lean.toJson digest.toString)]
  return 0
