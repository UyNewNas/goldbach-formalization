import Lean

/-!
NEW INPUT REPRESENTATION DIAGNOSTIC, cell 00 only.
The loader mechanically quotes the exact original file as List Char data.
geometryText00 is explicitly defined from that quoted list in this new owner.
No equality with an older String-literal declaration is asserted or assumed.
No JSON reader, typed decoder, or mathematics is executed by the loader.
-/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open Lean Elab Term

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CHARACTER_CORE before_loader_definition"
  err.flush

elab "originalGeometryChars00%" : term => do
  let s ← IO.FS.readFile "/workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json"
  let err ← IO.getStderr
  err.putStrLn "P26_CHARACTER_CORE loader_read_complete"
  err.flush
  let quoted := toExpr s.toList
  err.putStrLn "P26_CHARACTER_CORE loader_quote_complete"
  err.flush
  return quoted

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CHARACTER_CORE before_geometryChars00"
  err.flush

noncomputable def geometryChars00 : List Char := originalGeometryChars00%

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CHARACTER_CORE after_geometryChars00"
  err.flush

noncomputable def geometryText00 : String := String.ofList geometryChars00

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CHARACTER_CORE all_data_complete"
  err.flush

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
