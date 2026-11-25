import Lean

/-!
SOURCE ONLY / NOT COMPILED. One original cell00 String/character binding.
Both loaders read the same original file and retain its CRLF characters.
The character loader reuses the existing toExpr s.toList quotation; the
String loader uses the current saving16 IO.FS.readFile / Syntax.mkStrLit form.
No JSON parser, typed decoder, packed data, or mathematical checker is run.

The sole closed target below compares two local input declarations. It does
not yet identify oldString00 with the canonical originalText (0 : Fin 14),
whose current owner also contains the unresolved archive guards.
-/
namespace ImbalancedChen.P2Saving16StringCharBinding00

-- Retained from the existing CharacterCore diagnostic. This source-local
-- setting makes the effective maxRecDepth 1000000 inside this module.
-- No source maxHeartbeats, heap, warning, or linter override is introduced.
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open Lean Elab Term

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P25_STRING_CHAR_BINDING00 before_loader_definition"
  err.flush

elab "originalSaving16Chars00%" : term => do
  let s ← IO.FS.readFile "../goldbach-research/eighth-prefix-family-20261009-cell-00.witness.json"
  let err ← IO.getStderr
  err.putStrLn "P25_STRING_CHAR_BINDING00 loader_read_complete"
  err.flush
  let quoted := toExpr s.toList
  err.putStrLn "P25_STRING_CHAR_BINDING00 loader_quote_complete"
  err.flush
  return quoted

elab "originalSaving16Literal00%" : term => do
  let path := "../goldbach-research/eighth-prefix-family-20261009-cell-00.witness.json"
  let raw ← IO.FS.readFile path
  elabTerm (Syntax.mkStrLit raw) (some (mkConst ``String))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P25_STRING_CHAR_BINDING00 before_chars00"
  err.flush

noncomputable def chars00 : List Char := originalSaving16Chars00%

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P25_STRING_CHAR_BINDING00 before_oldString00"
  err.flush

noncomputable def oldString00 : String := originalSaving16Literal00%

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P25_STRING_CHAR_BINDING00 before_originalStringeq00"
  err.flush

theorem originalStringeq00 : String.ofList chars00 = oldString00 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P25_STRING_CHAR_BINDING00 after_originalStringeq00"
  err.flush

#print axioms originalStringeq00

end ImbalancedChen.P2Saving16StringCharBinding00
