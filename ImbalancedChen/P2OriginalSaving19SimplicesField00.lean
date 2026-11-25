import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01300

/-! Compose the complete original simplices array certificate into its original parent object.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def simplicesHeaderChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ']
noncomputable def simplicesFieldKey00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def simplicesFieldAcc00 : List (String × SourceJson) :=
  (simplicesFieldKey00, simplicesArrayValue00) :: faceLedgerFieldAcc00
noncomputable def simplicesSeparatorChars00 : List Char := [',']

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_field_after_data"
  err.flush

theorem geometryChars00_simplices_header_prefix :
    (geometryChars00.drop 100416).take 17 = simplicesHeaderChars00 := by rfl

theorem geometryChars00_simplices_header_split :
    geometryChars00.drop 100416 = simplicesHeaderChars00 ++ geometryChars00.drop 100433 := by
  calc
    geometryChars00.drop 100416 =
        (geometryChars00.drop 100416).take 17 ++ (geometryChars00.drop 100416).drop 17 :=
      (List.take_append_drop 17 (geometryChars00.drop 100416)).symm
    _ = simplicesHeaderChars00 ++ (geometryChars00.drop 100416).drop 17 :=
      congrArg (fun p => p ++ (geometryChars00.drop 100416).drop 17) geometryChars00_simplices_header_prefix
    _ = simplicesHeaderChars00 ++ geometryChars00.drop 100433 := by rw [List.drop_drop]

theorem geometryChars00_simplices_separator_prefix :
    (geometryChars00.drop 194776).take 1 = simplicesSeparatorChars00 := by rfl

theorem geometryChars00_simplices_separator_split :
    geometryChars00.drop 194776 = simplicesSeparatorChars00 ++ geometryChars00.drop 194777 := by
  calc
    geometryChars00.drop 194776 =
        (geometryChars00.drop 194776).take 1 ++ (geometryChars00.drop 194776).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 194776)).symm
    _ = simplicesSeparatorChars00 ++ (geometryChars00.drop 194776).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 194776).drop 1) geometryChars00_simplices_separator_prefix
    _ = simplicesSeparatorChars00 ++ geometryChars00.drop 194777 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_field_after_raw_bindings"
  err.flush

noncomputable def simplicesAfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending =>
      .ok (.obj (((simplicesFieldKey00, result.1) :: faceLedgerFieldAcc00).reverse), ending)
  | ',' :: ending =>
      SourceJson.object fuel (SourceJson.white ending)
        ((simplicesFieldKey00, result.1) :: faceLedgerFieldAcc00)
  | _ => .error "object separator missing"

theorem object_simplices_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (simplicesHeaderChars00 ++ rest)) faceLedgerFieldAcc00 =
      (SourceJson.value (fuel + 474) rest).bind (simplicesAfterValue00 (fuel + 474)) := by rfl

theorem simplices_after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (simplicesArrayValue00, simplicesSeparatorChars00 ++ tail)).bind
      (simplicesAfterValue00 (fuel + 474)) =
      SourceJson.object (fuel + 474) (SourceJson.white tail) simplicesFieldAcc00 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_field_after_generic_continuation"
  err.flush


theorem object_simplices_original (fuel : Nat) :
    SourceJson.object (fuel + 475) (SourceJson.white (geometryChars00.drop 100416)) faceLedgerFieldAcc00 =
      SourceJson.object (fuel + 474) (SourceJson.white (geometryChars00.drop 194777)) simplicesFieldAcc00 := by
  calc
    SourceJson.object (fuel + 475) (SourceJson.white (geometryChars00.drop 100416)) faceLedgerFieldAcc00 =
        SourceJson.object (fuel + 475)
          (SourceJson.white (simplicesHeaderChars00 ++ geometryChars00.drop 100433)) faceLedgerFieldAcc00 :=
      congrArg (fun s => SourceJson.object (fuel + 475) (SourceJson.white s) faceLedgerFieldAcc00)
        geometryChars00_simplices_header_split
    _ = (SourceJson.value (fuel + 474) (geometryChars00.drop 100433)).bind
        (simplicesAfterValue00 (fuel + 474)) :=
      object_simplices_header fuel (geometryChars00.drop 100433)
    _ = (Except.ok (simplicesArrayValue00, geometryChars00.drop 194776)).bind
        (simplicesAfterValue00 (fuel + 474)) :=
      congrArg (fun result => result.bind (simplicesAfterValue00 (fuel + 474)))
        (value_simplices_original (fuel + 0))
    _ = (Except.ok (simplicesArrayValue00,
          simplicesSeparatorChars00 ++ geometryChars00.drop 194777)).bind
        (simplicesAfterValue00 (fuel + 474)) :=
      congrArg (fun rest => (Except.ok (simplicesArrayValue00, rest)).bind
        (simplicesAfterValue00 (fuel + 474))) geometryChars00_simplices_separator_split
    _ = SourceJson.object (fuel + 474)
        (SourceJson.white (geometryChars00.drop 194777)) simplicesFieldAcc00 :=
      simplices_after_value_separator fuel (geometryChars00.drop 194777)

theorem geometryChars00_through_simplices :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195122 (SourceJson.white (geometryChars00.drop 194777)) simplicesFieldAcc00 := by
  exact geometryChars00_through_faceLedger.trans (object_simplices_original 194648)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_field_complete"
  err.flush

#print axioms geometryChars00_simplices_header_prefix
#print axioms geometryChars00_simplices_header_split
#print axioms geometryChars00_simplices_separator_prefix
#print axioms geometryChars00_simplices_separator_split
#print axioms object_simplices_header
#print axioms simplices_after_value_separator
#print axioms object_simplices_original
#print axioms geometryChars00_through_simplices

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
