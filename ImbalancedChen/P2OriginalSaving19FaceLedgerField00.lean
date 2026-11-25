import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00800

/-! Compose the complete original face_ledger array certificate into its original parent object.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def faceLedgerHeaderChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'f', 'a', 'c', 'e', '_', 'l', 'e', 'd', 'g', 'e', 'r', '"', ':', ' ']
noncomputable def faceLedgerFieldKey00 : String := String.ofList ['f', 'a', 'c', 'e', '_', 'l', 'e', 'd', 'g', 'e', 'r']
noncomputable def faceLedgerFieldAcc00 : List (String × SourceJson) :=
  (faceLedgerFieldKey00, faceLedgerArrayValue00) :: facetVerticesFieldAcc00
noncomputable def faceLedgerSeparatorChars00 : List Char := [',']

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_field_after_data"
  err.flush

theorem geometryChars00_faceLedger_header_prefix :
    (geometryChars00.drop 65221).take 19 = faceLedgerHeaderChars00 := by rfl

theorem geometryChars00_faceLedger_header_split :
    geometryChars00.drop 65221 = faceLedgerHeaderChars00 ++ geometryChars00.drop 65240 := by
  calc
    geometryChars00.drop 65221 =
        (geometryChars00.drop 65221).take 19 ++ (geometryChars00.drop 65221).drop 19 :=
      (List.take_append_drop 19 (geometryChars00.drop 65221)).symm
    _ = faceLedgerHeaderChars00 ++ (geometryChars00.drop 65221).drop 19 :=
      congrArg (fun p => p ++ (geometryChars00.drop 65221).drop 19) geometryChars00_faceLedger_header_prefix
    _ = faceLedgerHeaderChars00 ++ geometryChars00.drop 65240 := by rw [List.drop_drop]

theorem geometryChars00_faceLedger_separator_prefix :
    (geometryChars00.drop 100415).take 1 = faceLedgerSeparatorChars00 := by rfl

theorem geometryChars00_faceLedger_separator_split :
    geometryChars00.drop 100415 = faceLedgerSeparatorChars00 ++ geometryChars00.drop 100416 := by
  calc
    geometryChars00.drop 100415 =
        (geometryChars00.drop 100415).take 1 ++ (geometryChars00.drop 100415).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 100415)).symm
    _ = faceLedgerSeparatorChars00 ++ (geometryChars00.drop 100415).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 100415).drop 1) geometryChars00_faceLedger_separator_prefix
    _ = faceLedgerSeparatorChars00 ++ geometryChars00.drop 100416 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_field_after_raw_bindings"
  err.flush

noncomputable def faceLedgerAfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending =>
      .ok (.obj (((faceLedgerFieldKey00, result.1) :: facetVerticesFieldAcc00).reverse), ending)
  | ',' :: ending =>
      SourceJson.object fuel (SourceJson.white ending)
        ((faceLedgerFieldKey00, result.1) :: facetVerticesFieldAcc00)
  | _ => .error "object separator missing"

theorem object_faceLedger_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 57) (SourceJson.white (faceLedgerHeaderChars00 ++ rest)) facetVerticesFieldAcc00 =
      (SourceJson.value (fuel + 56) rest).bind (faceLedgerAfterValue00 (fuel + 56)) := by rfl

theorem faceLedger_after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (faceLedgerArrayValue00, faceLedgerSeparatorChars00 ++ tail)).bind
      (faceLedgerAfterValue00 (fuel + 56)) =
      SourceJson.object (fuel + 56) (SourceJson.white tail) faceLedgerFieldAcc00 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_field_after_generic_continuation"
  err.flush


theorem object_faceLedger_original (fuel : Nat) :
    SourceJson.object (fuel + 57) (SourceJson.white (geometryChars00.drop 65221)) facetVerticesFieldAcc00 =
      SourceJson.object (fuel + 56) (SourceJson.white (geometryChars00.drop 100416)) faceLedgerFieldAcc00 := by
  calc
    SourceJson.object (fuel + 57) (SourceJson.white (geometryChars00.drop 65221)) facetVerticesFieldAcc00 =
        SourceJson.object (fuel + 57)
          (SourceJson.white (faceLedgerHeaderChars00 ++ geometryChars00.drop 65240)) facetVerticesFieldAcc00 :=
      congrArg (fun s => SourceJson.object (fuel + 57) (SourceJson.white s) facetVerticesFieldAcc00)
        geometryChars00_faceLedger_header_split
    _ = (SourceJson.value (fuel + 56) (geometryChars00.drop 65240)).bind
        (faceLedgerAfterValue00 (fuel + 56)) :=
      object_faceLedger_header fuel (geometryChars00.drop 65240)
    _ = (Except.ok (faceLedgerArrayValue00, geometryChars00.drop 100415)).bind
        (faceLedgerAfterValue00 (fuel + 56)) :=
      congrArg (fun result => result.bind (faceLedgerAfterValue00 (fuel + 56)))
        (value_faceLedger_original (fuel + 0))
    _ = (Except.ok (faceLedgerArrayValue00,
          faceLedgerSeparatorChars00 ++ geometryChars00.drop 100416)).bind
        (faceLedgerAfterValue00 (fuel + 56)) :=
      congrArg (fun rest => (Except.ok (faceLedgerArrayValue00, rest)).bind
        (faceLedgerAfterValue00 (fuel + 56))) geometryChars00_faceLedger_separator_split
    _ = SourceJson.object (fuel + 56)
        (SourceJson.white (geometryChars00.drop 100416)) faceLedgerFieldAcc00 :=
      faceLedger_after_value_separator fuel (geometryChars00.drop 100416)

theorem geometryChars00_through_faceLedger :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195123 (SourceJson.white (geometryChars00.drop 100416)) faceLedgerFieldAcc00 := by
  exact geometryChars00_through_facetVertices.trans (object_faceLedger_original 195067)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_field_complete"
  err.flush

#print axioms geometryChars00_faceLedger_header_prefix
#print axioms geometryChars00_faceLedger_header_split
#print axioms geometryChars00_faceLedger_separator_prefix
#print axioms geometryChars00_faceLedger_separator_split
#print axioms object_faceLedger_header
#print axioms faceLedger_after_value_separator
#print axioms object_faceLedger_original
#print axioms geometryChars00_through_faceLedger

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
