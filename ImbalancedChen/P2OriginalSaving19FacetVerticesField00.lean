import ImbalancedChen.P2OriginalSaving19FacetVerticesArrayBlock00100

/-! Compose the complete original facet_vertices array certificate into its original parent object.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def facetVerticesHeaderChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ']
noncomputable def facetVerticesFieldKey00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def facetVerticesFieldAcc00 : List (String × SourceJson) :=
  (facetVerticesFieldKey00, facetVerticesArrayValue00) :: constraintMinimaFieldAcc00
noncomputable def facetVerticesSeparatorChars00 : List Char := [',']

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 facetVertices_field_after_data"
  err.flush

theorem geometryChars00_facetVertices_header_prefix :
    (geometryChars00.drop 62655).take 22 = facetVerticesHeaderChars00 := by rfl

theorem geometryChars00_facetVertices_header_split :
    geometryChars00.drop 62655 = facetVerticesHeaderChars00 ++ geometryChars00.drop 62677 := by
  calc
    geometryChars00.drop 62655 =
        (geometryChars00.drop 62655).take 22 ++ (geometryChars00.drop 62655).drop 22 :=
      (List.take_append_drop 22 (geometryChars00.drop 62655)).symm
    _ = facetVerticesHeaderChars00 ++ (geometryChars00.drop 62655).drop 22 :=
      congrArg (fun p => p ++ (geometryChars00.drop 62655).drop 22) geometryChars00_facetVertices_header_prefix
    _ = facetVerticesHeaderChars00 ++ geometryChars00.drop 62677 := by rw [List.drop_drop]

theorem geometryChars00_facetVertices_separator_prefix :
    (geometryChars00.drop 65220).take 1 = facetVerticesSeparatorChars00 := by rfl

theorem geometryChars00_facetVertices_separator_split :
    geometryChars00.drop 65220 = facetVerticesSeparatorChars00 ++ geometryChars00.drop 65221 := by
  calc
    geometryChars00.drop 65220 =
        (geometryChars00.drop 65220).take 1 ++ (geometryChars00.drop 65220).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 65220)).symm
    _ = facetVerticesSeparatorChars00 ++ (geometryChars00.drop 65220).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 65220).drop 1) geometryChars00_facetVertices_separator_prefix
    _ = facetVerticesSeparatorChars00 ++ geometryChars00.drop 65221 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 facetVertices_field_after_raw_bindings"
  err.flush

noncomputable def facetVerticesAfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending =>
      .ok (.obj (((facetVerticesFieldKey00, result.1) :: constraintMinimaFieldAcc00).reverse), ending)
  | ',' :: ending =>
      SourceJson.object fuel (SourceJson.white ending)
        ((facetVerticesFieldKey00, result.1) :: constraintMinimaFieldAcc00)
  | _ => .error "object separator missing"

theorem object_facetVertices_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 39) (SourceJson.white (facetVerticesHeaderChars00 ++ rest)) constraintMinimaFieldAcc00 =
      (SourceJson.value (fuel + 38) rest).bind (facetVerticesAfterValue00 (fuel + 38)) := by rfl

theorem facetVertices_after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (facetVerticesArrayValue00, facetVerticesSeparatorChars00 ++ tail)).bind
      (facetVerticesAfterValue00 (fuel + 38)) =
      SourceJson.object (fuel + 38) (SourceJson.white tail) facetVerticesFieldAcc00 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 facetVertices_field_after_generic_continuation"
  err.flush


theorem object_facetVertices_original (fuel : Nat) :
    SourceJson.object (fuel + 39) (SourceJson.white (geometryChars00.drop 62655)) constraintMinimaFieldAcc00 =
      SourceJson.object (fuel + 38) (SourceJson.white (geometryChars00.drop 65221)) facetVerticesFieldAcc00 := by
  calc
    SourceJson.object (fuel + 39) (SourceJson.white (geometryChars00.drop 62655)) constraintMinimaFieldAcc00 =
        SourceJson.object (fuel + 39)
          (SourceJson.white (facetVerticesHeaderChars00 ++ geometryChars00.drop 62677)) constraintMinimaFieldAcc00 :=
      congrArg (fun s => SourceJson.object (fuel + 39) (SourceJson.white s) constraintMinimaFieldAcc00)
        geometryChars00_facetVertices_header_split
    _ = (SourceJson.value (fuel + 38) (geometryChars00.drop 62677)).bind
        (facetVerticesAfterValue00 (fuel + 38)) :=
      object_facetVertices_header fuel (geometryChars00.drop 62677)
    _ = (Except.ok (facetVerticesArrayValue00, geometryChars00.drop 65220)).bind
        (facetVerticesAfterValue00 (fuel + 38)) :=
      congrArg (fun result => result.bind (facetVerticesAfterValue00 (fuel + 38)))
        (value_facetVertices_original (fuel + 0))
    _ = (Except.ok (facetVerticesArrayValue00,
          facetVerticesSeparatorChars00 ++ geometryChars00.drop 65221)).bind
        (facetVerticesAfterValue00 (fuel + 38)) :=
      congrArg (fun rest => (Except.ok (facetVerticesArrayValue00, rest)).bind
        (facetVerticesAfterValue00 (fuel + 38))) geometryChars00_facetVertices_separator_split
    _ = SourceJson.object (fuel + 38)
        (SourceJson.white (geometryChars00.drop 65221)) facetVerticesFieldAcc00 :=
      facetVertices_after_value_separator fuel (geometryChars00.drop 65221)

theorem geometryChars00_through_facetVertices :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195124 (SourceJson.white (geometryChars00.drop 65221)) facetVerticesFieldAcc00 := by
  exact geometryChars00_through_constraintMinima.trans (object_facetVertices_original 195086)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 facetVertices_field_complete"
  err.flush

#print axioms geometryChars00_facetVertices_header_prefix
#print axioms geometryChars00_facetVertices_header_split
#print axioms geometryChars00_facetVertices_separator_prefix
#print axioms geometryChars00_facetVertices_separator_split
#print axioms object_facetVertices_header
#print axioms facetVertices_after_value_separator
#print axioms object_facetVertices_original
#print axioms geometryChars00_through_facetVertices

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
