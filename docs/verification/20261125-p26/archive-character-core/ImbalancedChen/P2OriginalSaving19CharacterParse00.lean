import ImbalancedChen.P2OriginalSaving19CharacterLength00
import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput

/-! Pure original-reader success on the new input representation, cell 00 only.
The original SourceJson parser is imported unchanged. Its checked parse_ofList
bridge supplies the equivalent new String endpoint without an old-text premise.
No typed decoder, payload equality, other cell, or numerical row is checked. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CHARACTER_CORE before_parseChars_success_guard"
  err.flush

theorem geometryChars00_parse_success :
    (SourceJson.parseChars geometryChars00).toOption.isSome = true := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CHARACTER_CORE after_parseChars_success_guard"
  err.flush

theorem geometryText00_parse_success :
    (SourceJson.parse geometryText00).toOption.isSome = true := by
  rw [geometryText00, SourceJson.parse_ofList]
  exact geometryChars00_parse_success

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CHARACTER_CORE after_original_parser_new_text_success"
  err.flush

#print axioms geometryChars00_parse_success
#print axioms geometryText00_parse_success

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
