import ImbalancedChen.P2OriginalSaving19CharacterLength00
import ImbalancedChen.P2OriginalSaving19SourceJson

/-!
One exact original field, with the original CRLF bytes and trailing comma.
The candidate prefix and expected AST data are mechanically quoted from raw
bytes. Their relationship to the actual reader is certified by Lean below.
No host JSON parser, replacement reader, copied whole tail, or whole parse guard
is used. The final theorem is a first-field transition on the complete input;
it deliberately does not assert that the remaining object parses successfully.
-/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def dimensionPrefixChars00 : List Char := ['{', '\r', '\n', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '8', ',']

def dimensionKey00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']

def dimensionValue00 : SourceJson := .number (String.ofList ['8'])

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIMENSION_PREFIX before_actual_prefix_binding"
  err.flush

theorem geometryChars00_dimension_prefix :
    geometryChars00.take 20 = dimensionPrefixChars00 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIMENSION_PREFIX after_actual_prefix_binding"
  err.flush

/-- The comma is part of the checked prefix. The tail remains arbitrary.
The original object's empty-accumulator duplicate-key test is reduced here. -/
theorem value_dimension_prefix (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 12) (dimensionPrefixChars00 ++ tail) =
      SourceJson.object (fuel + 10) (SourceJson.white tail)
        [(dimensionKey00, dimensionValue00)] := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIMENSION_PREFIX after_generic_reader_step"
  err.flush

theorem geometryChars00_dimension_split :
    geometryChars00 = dimensionPrefixChars00 ++ geometryChars00.drop 20 := by
  exact (List.take_append_drop 20 geometryChars00).symm.trans
    (congrArg (fun p => p ++ geometryChars00.drop 20) geometryChars00_dimension_prefix)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIMENSION_PREFIX after_complete_input_split"
  err.flush

/-- Closed equality for the original reader on the complete original character
input. The remaining object call is retained, with its exact fuel and tail. -/
theorem geometryChars00_dimension_step :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195133 (SourceJson.white (geometryChars00.drop 20))
        [(dimensionKey00, dimensionValue00)] := by
  exact (congrArg (SourceJson.value 195135) geometryChars00_dimension_split).trans
    (value_dimension_prefix 195123 (geometryChars00.drop 20))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIMENSION_PREFIX after_closed_original_reader_step"
  err.flush

#print axioms geometryChars00_dimension_prefix
#print axioms value_dimension_prefix
#print axioms geometryChars00_dimension_split
#print axioms geometryChars00_dimension_step

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
