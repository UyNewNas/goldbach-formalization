import ImbalancedChen.P2OriginalSaving19ConstraintMinimaArrayBlock00100

/-! Compose the complete original all_original_constraint_minima array certificate into its original parent object.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def constraintMinimaHeaderChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'a', 'l', 'l', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', '_', 'm', 'i', 'n', 'i', 'm', 'a', '"', ':', ' ']
noncomputable def constraintMinimaFieldKey00 : String := String.ofList ['a', 'l', 'l', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', '_', 'm', 'i', 'n', 'i', 'm', 'a']
noncomputable def constraintMinimaFieldAcc00 : List (String × SourceJson) :=
  (constraintMinimaFieldKey00, constraintMinimaArrayValue00) :: vertexValuesFieldAcc00
noncomputable def constraintMinimaSeparatorChars00 : List Char := [',']

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_field_after_data"
  err.flush

theorem geometryChars00_constraintMinima_header_prefix :
    (geometryChars00.drop 60449).take 38 = constraintMinimaHeaderChars00 := by rfl

theorem geometryChars00_constraintMinima_header_split :
    geometryChars00.drop 60449 = constraintMinimaHeaderChars00 ++ geometryChars00.drop 60487 := by
  calc
    geometryChars00.drop 60449 =
        (geometryChars00.drop 60449).take 38 ++ (geometryChars00.drop 60449).drop 38 :=
      (List.take_append_drop 38 (geometryChars00.drop 60449)).symm
    _ = constraintMinimaHeaderChars00 ++ (geometryChars00.drop 60449).drop 38 :=
      congrArg (fun p => p ++ (geometryChars00.drop 60449).drop 38) geometryChars00_constraintMinima_header_prefix
    _ = constraintMinimaHeaderChars00 ++ geometryChars00.drop 60487 := by rw [List.drop_drop]

theorem geometryChars00_constraintMinima_separator_prefix :
    (geometryChars00.drop 62654).take 1 = constraintMinimaSeparatorChars00 := by rfl

theorem geometryChars00_constraintMinima_separator_split :
    geometryChars00.drop 62654 = constraintMinimaSeparatorChars00 ++ geometryChars00.drop 62655 := by
  calc
    geometryChars00.drop 62654 =
        (geometryChars00.drop 62654).take 1 ++ (geometryChars00.drop 62654).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 62654)).symm
    _ = constraintMinimaSeparatorChars00 ++ (geometryChars00.drop 62654).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 62654).drop 1) geometryChars00_constraintMinima_separator_prefix
    _ = constraintMinimaSeparatorChars00 ++ geometryChars00.drop 62655 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_field_after_raw_bindings"
  err.flush

noncomputable def constraintMinimaAfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending =>
      .ok (.obj (((constraintMinimaFieldKey00, result.1) :: vertexValuesFieldAcc00).reverse), ending)
  | ',' :: ending =>
      SourceJson.object fuel (SourceJson.white ending)
        ((constraintMinimaFieldKey00, result.1) :: vertexValuesFieldAcc00)
  | _ => .error "object separator missing"

theorem object_constraintMinima_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 118) (SourceJson.white (constraintMinimaHeaderChars00 ++ rest)) vertexValuesFieldAcc00 =
      (SourceJson.value (fuel + 117) rest).bind (constraintMinimaAfterValue00 (fuel + 117)) := by rfl

theorem constraintMinima_after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (constraintMinimaArrayValue00, constraintMinimaSeparatorChars00 ++ tail)).bind
      (constraintMinimaAfterValue00 (fuel + 117)) =
      SourceJson.object (fuel + 117) (SourceJson.white tail) constraintMinimaFieldAcc00 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_field_after_generic_continuation"
  err.flush


theorem object_constraintMinima_original (fuel : Nat) :
    SourceJson.object (fuel + 118) (SourceJson.white (geometryChars00.drop 60449)) vertexValuesFieldAcc00 =
      SourceJson.object (fuel + 117) (SourceJson.white (geometryChars00.drop 62655)) constraintMinimaFieldAcc00 := by
  calc
    SourceJson.object (fuel + 118) (SourceJson.white (geometryChars00.drop 60449)) vertexValuesFieldAcc00 =
        SourceJson.object (fuel + 118)
          (SourceJson.white (constraintMinimaHeaderChars00 ++ geometryChars00.drop 60487)) vertexValuesFieldAcc00 :=
      congrArg (fun s => SourceJson.object (fuel + 118) (SourceJson.white s) vertexValuesFieldAcc00)
        geometryChars00_constraintMinima_header_split
    _ = (SourceJson.value (fuel + 117) (geometryChars00.drop 60487)).bind
        (constraintMinimaAfterValue00 (fuel + 117)) :=
      object_constraintMinima_header fuel (geometryChars00.drop 60487)
    _ = (Except.ok (constraintMinimaArrayValue00, geometryChars00.drop 62654)).bind
        (constraintMinimaAfterValue00 (fuel + 117)) :=
      congrArg (fun result => result.bind (constraintMinimaAfterValue00 (fuel + 117)))
        (value_constraintMinima_original (fuel + 0))
    _ = (Except.ok (constraintMinimaArrayValue00,
          constraintMinimaSeparatorChars00 ++ geometryChars00.drop 62655)).bind
        (constraintMinimaAfterValue00 (fuel + 117)) :=
      congrArg (fun rest => (Except.ok (constraintMinimaArrayValue00, rest)).bind
        (constraintMinimaAfterValue00 (fuel + 117))) geometryChars00_constraintMinima_separator_split
    _ = SourceJson.object (fuel + 117)
        (SourceJson.white (geometryChars00.drop 62655)) constraintMinimaFieldAcc00 :=
      constraintMinima_after_value_separator fuel (geometryChars00.drop 62655)

theorem geometryChars00_through_constraintMinima :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195125 (SourceJson.white (geometryChars00.drop 62655)) constraintMinimaFieldAcc00 := by
  exact geometryChars00_through_vertexValues.trans (object_constraintMinima_original 195008)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_field_complete"
  err.flush

#print axioms geometryChars00_constraintMinima_header_prefix
#print axioms geometryChars00_constraintMinima_header_split
#print axioms geometryChars00_constraintMinima_separator_prefix
#print axioms geometryChars00_constraintMinima_separator_split
#print axioms object_constraintMinima_header
#print axioms constraintMinima_after_value_separator
#print axioms object_constraintMinima_original
#print axioms geometryChars00_through_constraintMinima

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
