import ImbalancedChen.P2OriginalSaving19Moment01Metadata
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock035
import ImbalancedChen.P2OriginalSaving19ParseFromValue00

/-! Whole original moment01 pure SourceJson parse, assembled from checked compact-input spans. No typed decode claim.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsHeaderChars : List Char := ['\r', '\n', ' ', ' ', '"', 'r', 'e', 'c', 'o', 'r', 'd', 's', '"', ':', ' ']
noncomputable def momentRecordsFieldKey : String := String.ofList ['r', 'e', 'c', 'o', 'r', 'd', 's']
noncomputable def momentRecordsFieldAcc : List (String × SourceJson) :=
  (momentRecordsFieldKey, momentRecordsArrayValue) :: momentMetadataAcc009
noncomputable def momentRootValue : SourceJson := .obj (momentRecordsFieldAcc.reverse)
noncomputable def momentRecordsSeparatorChars : List Char := ['\r', '\n', '}']
noncomputable def momentTrailingChars : List Char := ['\r', '\n']

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 whole_before_last_header_binding"
  err.flush

theorem moment_records_header_prefix :
    (momentRest01 348).take 15 = momentRecordsHeaderChars := by rfl

theorem moment_records_header_split :
    momentRest01 348 = momentRecordsHeaderChars ++ momentRest01 363 := by
  calc
    momentRest01 348 =
        (momentRest01 348).take 15 ++ (momentRest01 348).drop 15 :=
      (List.take_append_drop 15 (momentRest01 348)).symm
    _ = momentRecordsHeaderChars ++ (momentRest01 348).drop 15 :=
      congrArg (fun p => p ++ (momentRest01 348).drop 15) moment_records_header_prefix
    _ = momentRecordsHeaderChars ++ momentRest01 363 :=
      congrArg (fun rest => momentRecordsHeaderChars ++ rest) (momentRest01_drop 348 15)

theorem moment_records_separator_prefix :
    (momentRest01 75089).take 3 = momentRecordsSeparatorChars := by rfl

theorem moment_records_separator_split :
    momentRest01 75089 = momentRecordsSeparatorChars ++ momentRest01 75092 := by
  calc
    momentRest01 75089 =
        (momentRest01 75089).take 3 ++ (momentRest01 75089).drop 3 :=
      (List.take_append_drop 3 (momentRest01 75089)).symm
    _ = momentRecordsSeparatorChars ++ (momentRest01 75089).drop 3 :=
      congrArg (fun p => p ++ (momentRest01 75089).drop 3) moment_records_separator_prefix
    _ = momentRecordsSeparatorChars ++ momentRest01 75092 :=
      congrArg (fun rest => momentRecordsSeparatorChars ++ rest) (momentRest01_drop 75089 3)

theorem moment_trailing_prefix :
    (momentRest01 75092).take 2 = momentTrailingChars := by rfl

theorem moment_trailing_split :
    momentRest01 75092 = momentTrailingChars ++ momentRest01 75094 := by
  calc
    momentRest01 75092 =
        (momentRest01 75092).take 2 ++ (momentRest01 75092).drop 2 :=
      (List.take_append_drop 2 (momentRest01 75092)).symm
    _ = momentTrailingChars ++ (momentRest01 75092).drop 2 :=
      congrArg (fun p => p ++ (momentRest01 75092).drop 2) moment_trailing_prefix
    _ = momentTrailingChars ++ momentRest01 75094 :=
      congrArg (fun rest => momentTrailingChars ++ rest) (momentRest01_drop 75092 2)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 whole_after_last_raw_bindings"
  err.flush

noncomputable def momentRecordsAfterValue (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending =>
      .ok (.obj (((momentRecordsFieldKey, result.1) :: momentMetadataAcc009).reverse), ending)
  | ',' :: ending =>
      SourceJson.object fuel (SourceJson.white ending)
        ((momentRecordsFieldKey, result.1) :: momentMetadataAcc009)
  | _ => .error "object separator missing"

theorem object_moment_records_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 183) (SourceJson.white (momentRecordsHeaderChars ++ rest)) momentMetadataAcc009 =
      (SourceJson.value (fuel + 182) rest).bind (momentRecordsAfterValue (fuel + 182)) := by rfl

theorem moment_records_after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (momentRecordsArrayValue, momentRecordsSeparatorChars ++ tail)).bind
      (momentRecordsAfterValue (fuel + 182)) = .ok (momentRootValue, tail) := by rfl

theorem object_moment_records_original (fuel : Nat) :
    SourceJson.object (fuel + 183) (SourceJson.white (momentRest01 348)) momentMetadataAcc009 =
      .ok (momentRootValue, momentRest01 75092) := by
  calc
    SourceJson.object (fuel + 183) (SourceJson.white (momentRest01 348)) momentMetadataAcc009 =
        SourceJson.object (fuel + 183)
          (SourceJson.white (momentRecordsHeaderChars ++ momentRest01 363)) momentMetadataAcc009 :=
      congrArg (fun rest => SourceJson.object (fuel + 183) (SourceJson.white rest) momentMetadataAcc009)
        moment_records_header_split
    _ = (SourceJson.value (fuel + 182) (momentRest01 363)).bind
        (momentRecordsAfterValue (fuel + 182)) :=
      object_moment_records_header fuel (momentRest01 363)
    _ = (Except.ok (momentRecordsArrayValue, momentRest01 75089)).bind
        (momentRecordsAfterValue (fuel + 182)) :=
      congrArg (fun result => result.bind (momentRecordsAfterValue (fuel + 182)))
        (value_moment_records_original fuel)
    _ = (Except.ok (momentRecordsArrayValue,
          momentRecordsSeparatorChars ++ momentRest01 75092)).bind
        (momentRecordsAfterValue (fuel + 182)) :=
      congrArg (fun rest => (Except.ok (momentRecordsArrayValue, rest)).bind
        (momentRecordsAfterValue (fuel + 182))) moment_records_separator_split
    _ = .ok (momentRootValue, momentRest01 75092) :=
      moment_records_after_value_separator fuel (momentRest01 75092)

theorem value_moment01_original (fuel : Nat) :
    SourceJson.value (fuel + 193) momentChars01 =
      .ok (momentRootValue, momentRest01 75092) := by
  exact (momentChars01_through_metadata fuel).trans (object_moment_records_original fuel)

theorem momentTrailing_white : SourceJson.white (momentRest01 75092) = [] := by
  calc
    SourceJson.white (momentRest01 75092) =
        SourceJson.white (momentTrailingChars ++ momentRest01 75094) :=
      congrArg SourceJson.white moment_trailing_split
    _ = SourceJson.white (momentTrailingChars ++ []) :=
      congrArg (fun rest => SourceJson.white (momentTrailingChars ++ rest)) momentRest01_end
    _ = [] := by rfl

theorem momentChars01_parseChars : SourceJson.parseChars momentChars01 = .ok momentRootValue := by
  apply SourceJson.parseChars_of_value_eq (tail := momentRest01 75092)
  · rw [momentChars01_length]
    exact value_moment01_original 74902
  · exact momentTrailing_white

theorem momentPacked01_parseChars :
    SourceJson.parseChars momentPacked01.toList = .ok momentRootValue :=
  momentChars01_parseChars

theorem momentPacked01_parse :
    SourceJson.parse (String.ofList momentPacked01.toList) = .ok momentRootValue :=
  (SourceJson.parse_ofList momentPacked01.toList).trans momentPacked01_parseChars

theorem momentPacked01_parse_success :
    (SourceJson.parse (String.ofList momentPacked01.toList)).toOption.isSome = true := by
  rw [momentPacked01_parse]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 whole_original_parser_complete"
  err.flush

#print axioms moment_records_header_prefix
#print axioms moment_records_header_split
#print axioms moment_records_separator_prefix
#print axioms moment_records_separator_split
#print axioms moment_trailing_prefix
#print axioms moment_trailing_split
#print axioms object_moment_records_header
#print axioms moment_records_after_value_separator
#print axioms object_moment_records_original
#print axioms value_moment01_original
#print axioms momentTrailing_white
#print axioms momentChars01_parseChars
#print axioms momentPacked01_parseChars
#print axioms momentPacked01_parse
#print axioms momentPacked01_parse_success

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
