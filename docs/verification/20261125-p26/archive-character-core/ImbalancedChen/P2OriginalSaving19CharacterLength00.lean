import ImbalancedChen.P2OriginalSaving19CharacterCore00

/-! Closed length guard on the new explicitly quoted character input.
This does not compute the old whole String.toList or assert old-text equality. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CHARACTER_CORE before_chars_length_guard"
  err.flush

theorem geometryChars00_length : geometryChars00.length = 195134 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CHARACTER_CORE after_chars_length_guard"
  err.flush

#print axioms geometryChars00_length

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
