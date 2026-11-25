import ImbalancedChen.P2OriginalSaving19Moment00Metadata
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock013
import ImbalancedChen.P2OriginalSaving19ParseFromValue00

/-! Whole original moment00 pure SourceJson parse, assembled from checked compact-input spans. No typed decode claim.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Parsing
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
  err.putStrLn "P26_MOMENT00 whole_before_last_header_binding"
  err.flush

theorem moment_records_header_prefix :
    (momentRest00 348).take 15 = momentRecordsHeaderChars := by rfl

theorem moment_records_header_split :
    momentRest00 348 = momentRecordsHeaderChars ++ momentRest00 363 := by
  calc
    momentRest00 348 =
        (momentRest00 348).take 15 ++ (momentRest00 348).drop 15 :=
      (List.take_append_drop 15 (momentRest00 348)).symm
    _ = momentRecordsHeaderChars ++ (momentRest00 348).drop 15 :=
      congrArg (fun p => p ++ (momentRest00 348).drop 15) moment_records_header_prefix
    _ = momentRecordsHeaderChars ++ momentRest00 363 :=
      congrArg (fun rest => momentRecordsHeaderChars ++ rest) (momentRest00_drop 348 15)

theorem moment_records_separator_prefix :
    (momentRest00 28994).take 3 = momentRecordsSeparatorChars := by rfl

theorem moment_records_separator_split :
    momentRest00 28994 = momentRecordsSeparatorChars ++ momentRest00 28997 := by
  calc
    momentRest00 28994 =
        (momentRest00 28994).take 3 ++ (momentRest00 28994).drop 3 :=
      (List.take_append_drop 3 (momentRest00 28994)).symm
    _ = momentRecordsSeparatorChars ++ (momentRest00 28994).drop 3 :=
      congrArg (fun p => p ++ (momentRest00 28994).drop 3) moment_records_separator_prefix
    _ = momentRecordsSeparatorChars ++ momentRest00 28997 :=
      congrArg (fun rest => momentRecordsSeparatorChars ++ rest) (momentRest00_drop 28994 3)

theorem moment_trailing_prefix :
    (momentRest00 28997).take 2 = momentTrailingChars := by rfl

theorem moment_trailing_split :
    momentRest00 28997 = momentTrailingChars ++ momentRest00 28999 := by
  calc
    momentRest00 28997 =
        (momentRest00 28997).take 2 ++ (momentRest00 28997).drop 2 :=
      (List.take_append_drop 2 (momentRest00 28997)).symm
    _ = momentTrailingChars ++ (momentRest00 28997).drop 2 :=
      congrArg (fun p => p ++ (momentRest00 28997).drop 2) moment_trailing_prefix
    _ = momentTrailingChars ++ momentRest00 28999 :=
      congrArg (fun rest => momentTrailingChars ++ rest) (momentRest00_drop 28997 2)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 whole_after_last_raw_bindings"
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
    SourceJson.object (fuel + 95) (SourceJson.white (momentRecordsHeaderChars ++ rest)) momentMetadataAcc009 =
      (SourceJson.value (fuel + 94) rest).bind (momentRecordsAfterValue (fuel + 94)) := by rfl

theorem moment_records_after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (momentRecordsArrayValue, momentRecordsSeparatorChars ++ tail)).bind
      (momentRecordsAfterValue (fuel + 94)) = .ok (momentRootValue, tail) := by rfl

theorem object_moment_records_original (fuel : Nat) :
    SourceJson.object (fuel + 95) (SourceJson.white (momentRest00 348)) momentMetadataAcc009 =
      .ok (momentRootValue, momentRest00 28997) := by
  calc
    SourceJson.object (fuel + 95) (SourceJson.white (momentRest00 348)) momentMetadataAcc009 =
        SourceJson.object (fuel + 95)
          (SourceJson.white (momentRecordsHeaderChars ++ momentRest00 363)) momentMetadataAcc009 :=
      congrArg (fun rest => SourceJson.object (fuel + 95) (SourceJson.white rest) momentMetadataAcc009)
        moment_records_header_split
    _ = (SourceJson.value (fuel + 94) (momentRest00 363)).bind
        (momentRecordsAfterValue (fuel + 94)) :=
      object_moment_records_header fuel (momentRest00 363)
    _ = (Except.ok (momentRecordsArrayValue, momentRest00 28994)).bind
        (momentRecordsAfterValue (fuel + 94)) :=
      congrArg (fun result => result.bind (momentRecordsAfterValue (fuel + 94)))
        (value_moment_records_original fuel)
    _ = (Except.ok (momentRecordsArrayValue,
          momentRecordsSeparatorChars ++ momentRest00 28997)).bind
        (momentRecordsAfterValue (fuel + 94)) :=
      congrArg (fun rest => (Except.ok (momentRecordsArrayValue, rest)).bind
        (momentRecordsAfterValue (fuel + 94))) moment_records_separator_split
    _ = .ok (momentRootValue, momentRest00 28997) :=
      moment_records_after_value_separator fuel (momentRest00 28997)

theorem value_moment00_original (fuel : Nat) :
    SourceJson.value (fuel + 105) momentChars00 =
      .ok (momentRootValue, momentRest00 28997) := by
  exact (momentChars00_through_metadata fuel).trans (object_moment_records_original fuel)

theorem momentTrailing_white : SourceJson.white (momentRest00 28997) = [] := by
  calc
    SourceJson.white (momentRest00 28997) =
        SourceJson.white (momentTrailingChars ++ momentRest00 28999) :=
      congrArg SourceJson.white moment_trailing_split
    _ = SourceJson.white (momentTrailingChars ++ []) :=
      congrArg (fun rest => SourceJson.white (momentTrailingChars ++ rest)) momentRest00_end
    _ = [] := by rfl

theorem momentChars00_parseChars : SourceJson.parseChars momentChars00 = .ok momentRootValue := by
  apply SourceJson.parseChars_of_value_eq (tail := momentRest00 28997)
  · rw [momentChars00_length]
    exact value_moment00_original 28895
  · exact momentTrailing_white

theorem momentPacked00_parseChars :
    SourceJson.parseChars momentPacked00.toList = .ok momentRootValue :=
  momentChars00_parseChars

theorem momentPacked00_parse :
    SourceJson.parse (String.ofList momentPacked00.toList) = .ok momentRootValue :=
  (SourceJson.parse_ofList momentPacked00.toList).trans momentPacked00_parseChars

theorem momentPacked00_parse_success :
    (SourceJson.parse (String.ofList momentPacked00.toList)).toOption.isSome = true := by
  rw [momentPacked00_parse]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 whole_original_parser_complete"
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
#print axioms value_moment00_original
#print axioms momentTrailing_white
#print axioms momentChars00_parseChars
#print axioms momentPacked00_parseChars
#print axioms momentPacked00_parse
#print axioms momentPacked00_parse_success

end ImbalancedChen.P2OriginalSaving19Moment00Parsing
