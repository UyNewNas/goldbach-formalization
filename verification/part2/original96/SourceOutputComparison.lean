import Lean
import ImbalancedChen.Certificates.P2OriginalLog96

open ImbalancedChen.Certificates.P2OriginalLog96

def main (args : List String) : IO Unit := do
  let [inputPath] := args | throw (IO.userError "expected an input JSON path")
  let input ← IO.FS.readFile inputPath
  let parsed : Except String (Array (Array Int)) := Lean.Json.parse input >>= Lean.fromJson?
  let .ok rows := parsed | throw (IO.userError "invalid input JSON")
  let mut output : Array (Array Int) := #[]
  for row in rows do
    if row.size != 2 then
      throw (IO.userError "expected a numerator and denominator")
    let numerator := row[0]!
    let denominator := row[1]!
    if denominator <= 0 then
      throw (IO.userError "expected a positive denominator")
    let (lower, upper) := logInterval ((numerator : ℚ) / (denominator : ℚ))
    output := output.push #[numerator, denominator, lower, upper]
  IO.println (Lean.toJson output).compress
