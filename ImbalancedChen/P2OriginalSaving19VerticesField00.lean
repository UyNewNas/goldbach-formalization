import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00300

/-! Compose the complete original vertices array certificate into its original parent object.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def verticesHeaderChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ']
noncomputable def verticesFieldKey00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def verticesFieldAcc00 : List (String × SourceJson) :=
  (verticesFieldKey00, verticesArrayValue00) :: active8FieldAcc00
noncomputable def verticesSeparatorChars00 : List Char := [',']

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_field_after_data"
  err.flush

theorem geometryChars00_vertices_header_prefix :
    (geometryChars00.drop 40598).take 16 = verticesHeaderChars00 := by rfl

theorem geometryChars00_vertices_header_split :
    geometryChars00.drop 40598 = verticesHeaderChars00 ++ geometryChars00.drop 40614 := by
  calc
    geometryChars00.drop 40598 =
        (geometryChars00.drop 40598).take 16 ++ (geometryChars00.drop 40598).drop 16 :=
      (List.take_append_drop 16 (geometryChars00.drop 40598)).symm
    _ = verticesHeaderChars00 ++ (geometryChars00.drop 40598).drop 16 :=
      congrArg (fun p => p ++ (geometryChars00.drop 40598).drop 16) geometryChars00_vertices_header_prefix
    _ = verticesHeaderChars00 ++ geometryChars00.drop 40614 := by rw [List.drop_drop]

theorem geometryChars00_vertices_separator_prefix :
    (geometryChars00.drop 46974).take 1 = verticesSeparatorChars00 := by rfl

theorem geometryChars00_vertices_separator_split :
    geometryChars00.drop 46974 = verticesSeparatorChars00 ++ geometryChars00.drop 46975 := by
  calc
    geometryChars00.drop 46974 =
        (geometryChars00.drop 46974).take 1 ++ (geometryChars00.drop 46974).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 46974)).symm
    _ = verticesSeparatorChars00 ++ (geometryChars00.drop 46974).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 46974).drop 1) geometryChars00_vertices_separator_prefix
    _ = verticesSeparatorChars00 ++ geometryChars00.drop 46975 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_field_after_raw_bindings"
  err.flush

noncomputable def verticesAfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending =>
      .ok (.obj (((verticesFieldKey00, result.1) :: active8FieldAcc00).reverse), ending)
  | ',' :: ending =>
      SourceJson.object fuel (SourceJson.white ending)
        ((verticesFieldKey00, result.1) :: active8FieldAcc00)
  | _ => .error "object separator missing"

theorem object_vertices_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 56) (SourceJson.white (verticesHeaderChars00 ++ rest)) active8FieldAcc00 =
      (SourceJson.value (fuel + 55) rest).bind (verticesAfterValue00 (fuel + 55)) := by rfl

theorem vertices_after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (verticesArrayValue00, verticesSeparatorChars00 ++ tail)).bind
      (verticesAfterValue00 (fuel + 55)) =
      SourceJson.object (fuel + 55) (SourceJson.white tail) verticesFieldAcc00 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_field_after_generic_continuation"
  err.flush


theorem object_vertices_original (fuel : Nat) :
    SourceJson.object (fuel + 56) (SourceJson.white (geometryChars00.drop 40598)) active8FieldAcc00 =
      SourceJson.object (fuel + 55) (SourceJson.white (geometryChars00.drop 46975)) verticesFieldAcc00 := by
  calc
    SourceJson.object (fuel + 56) (SourceJson.white (geometryChars00.drop 40598)) active8FieldAcc00 =
        SourceJson.object (fuel + 56)
          (SourceJson.white (verticesHeaderChars00 ++ geometryChars00.drop 40614)) active8FieldAcc00 :=
      congrArg (fun s => SourceJson.object (fuel + 56) (SourceJson.white s) active8FieldAcc00)
        geometryChars00_vertices_header_split
    _ = (SourceJson.value (fuel + 55) (geometryChars00.drop 40614)).bind
        (verticesAfterValue00 (fuel + 55)) :=
      object_vertices_header fuel (geometryChars00.drop 40614)
    _ = (Except.ok (verticesArrayValue00, geometryChars00.drop 46974)).bind
        (verticesAfterValue00 (fuel + 55)) :=
      congrArg (fun result => result.bind (verticesAfterValue00 (fuel + 55)))
        (value_vertices_original (fuel + 0))
    _ = (Except.ok (verticesArrayValue00,
          verticesSeparatorChars00 ++ geometryChars00.drop 46975)).bind
        (verticesAfterValue00 (fuel + 55)) :=
      congrArg (fun rest => (Except.ok (verticesArrayValue00, rest)).bind
        (verticesAfterValue00 (fuel + 55))) geometryChars00_vertices_separator_split
    _ = SourceJson.object (fuel + 55)
        (SourceJson.white (geometryChars00.drop 46975)) verticesFieldAcc00 :=
      vertices_after_value_separator fuel (geometryChars00.drop 46975)

theorem geometryChars00_through_vertices :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195127 (SourceJson.white (geometryChars00.drop 46975)) verticesFieldAcc00 := by
  exact geometryChars00_through_active8.trans (object_vertices_original 195072)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_field_complete"
  err.flush

#print axioms geometryChars00_vertices_header_prefix
#print axioms geometryChars00_vertices_header_split
#print axioms geometryChars00_vertices_separator_prefix
#print axioms geometryChars00_vertices_separator_split
#print axioms object_vertices_header
#print axioms vertices_after_value_separator
#print axioms object_vertices_original
#print axioms geometryChars00_through_vertices

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
