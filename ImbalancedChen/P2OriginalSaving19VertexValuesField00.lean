import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00600

/-! Compose the complete original vertex_values array certificate into its original parent object.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def vertexValuesHeaderChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'v', 'a', 'l', 'u', 'e', 's', '"', ':', ' ']
noncomputable def vertexValuesFieldKey00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'v', 'a', 'l', 'u', 'e', 's']
noncomputable def vertexValuesFieldAcc00 : List (String × SourceJson) :=
  (vertexValuesFieldKey00, vertexValuesArrayValue00) :: verticesFieldAcc00
noncomputable def vertexValuesSeparatorChars00 : List Char := [',']

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_field_after_data"
  err.flush

theorem geometryChars00_vertexValues_header_prefix :
    (geometryChars00.drop 46975).take 21 = vertexValuesHeaderChars00 := by rfl

theorem geometryChars00_vertexValues_header_split :
    geometryChars00.drop 46975 = vertexValuesHeaderChars00 ++ geometryChars00.drop 46996 := by
  calc
    geometryChars00.drop 46975 =
        (geometryChars00.drop 46975).take 21 ++ (geometryChars00.drop 46975).drop 21 :=
      (List.take_append_drop 21 (geometryChars00.drop 46975)).symm
    _ = vertexValuesHeaderChars00 ++ (geometryChars00.drop 46975).drop 21 :=
      congrArg (fun p => p ++ (geometryChars00.drop 46975).drop 21) geometryChars00_vertexValues_header_prefix
    _ = vertexValuesHeaderChars00 ++ geometryChars00.drop 46996 := by rw [List.drop_drop]

theorem geometryChars00_vertexValues_separator_prefix :
    (geometryChars00.drop 60448).take 1 = vertexValuesSeparatorChars00 := by rfl

theorem geometryChars00_vertexValues_separator_split :
    geometryChars00.drop 60448 = vertexValuesSeparatorChars00 ++ geometryChars00.drop 60449 := by
  calc
    geometryChars00.drop 60448 =
        (geometryChars00.drop 60448).take 1 ++ (geometryChars00.drop 60448).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 60448)).symm
    _ = vertexValuesSeparatorChars00 ++ (geometryChars00.drop 60448).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 60448).drop 1) geometryChars00_vertexValues_separator_prefix
    _ = vertexValuesSeparatorChars00 ++ geometryChars00.drop 60449 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_field_after_raw_bindings"
  err.flush

noncomputable def vertexValuesAfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending =>
      .ok (.obj (((vertexValuesFieldKey00, result.1) :: verticesFieldAcc00).reverse), ending)
  | ',' :: ending =>
      SourceJson.object fuel (SourceJson.white ending)
        ((vertexValuesFieldKey00, result.1) :: verticesFieldAcc00)
  | _ => .error "object separator missing"

theorem object_vertexValues_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 65) (SourceJson.white (vertexValuesHeaderChars00 ++ rest)) verticesFieldAcc00 =
      (SourceJson.value (fuel + 64) rest).bind (vertexValuesAfterValue00 (fuel + 64)) := by rfl

theorem vertexValues_after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (vertexValuesArrayValue00, vertexValuesSeparatorChars00 ++ tail)).bind
      (vertexValuesAfterValue00 (fuel + 64)) =
      SourceJson.object (fuel + 64) (SourceJson.white tail) vertexValuesFieldAcc00 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_field_after_generic_continuation"
  err.flush


theorem object_vertexValues_original (fuel : Nat) :
    SourceJson.object (fuel + 65) (SourceJson.white (geometryChars00.drop 46975)) verticesFieldAcc00 =
      SourceJson.object (fuel + 64) (SourceJson.white (geometryChars00.drop 60449)) vertexValuesFieldAcc00 := by
  calc
    SourceJson.object (fuel + 65) (SourceJson.white (geometryChars00.drop 46975)) verticesFieldAcc00 =
        SourceJson.object (fuel + 65)
          (SourceJson.white (vertexValuesHeaderChars00 ++ geometryChars00.drop 46996)) verticesFieldAcc00 :=
      congrArg (fun s => SourceJson.object (fuel + 65) (SourceJson.white s) verticesFieldAcc00)
        geometryChars00_vertexValues_header_split
    _ = (SourceJson.value (fuel + 64) (geometryChars00.drop 46996)).bind
        (vertexValuesAfterValue00 (fuel + 64)) :=
      object_vertexValues_header fuel (geometryChars00.drop 46996)
    _ = (Except.ok (vertexValuesArrayValue00, geometryChars00.drop 60448)).bind
        (vertexValuesAfterValue00 (fuel + 64)) :=
      congrArg (fun result => result.bind (vertexValuesAfterValue00 (fuel + 64)))
        (value_vertexValues_original (fuel + 0))
    _ = (Except.ok (vertexValuesArrayValue00,
          vertexValuesSeparatorChars00 ++ geometryChars00.drop 60449)).bind
        (vertexValuesAfterValue00 (fuel + 64)) :=
      congrArg (fun rest => (Except.ok (vertexValuesArrayValue00, rest)).bind
        (vertexValuesAfterValue00 (fuel + 64))) geometryChars00_vertexValues_separator_split
    _ = SourceJson.object (fuel + 64)
        (SourceJson.white (geometryChars00.drop 60449)) vertexValuesFieldAcc00 :=
      vertexValues_after_value_separator fuel (geometryChars00.drop 60449)

theorem geometryChars00_through_vertexValues :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195126 (SourceJson.white (geometryChars00.drop 60449)) vertexValuesFieldAcc00 := by
  exact geometryChars00_through_vertices.trans (object_vertexValues_original 195062)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_field_complete"
  err.flush

#print axioms geometryChars00_vertexValues_header_prefix
#print axioms geometryChars00_vertexValues_header_split
#print axioms geometryChars00_vertexValues_separator_prefix
#print axioms geometryChars00_vertexValues_separator_split
#print axioms object_vertexValues_header
#print axioms vertexValues_after_value_separator
#print axioms object_vertexValues_original
#print axioms geometryChars00_through_vertexValues

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
