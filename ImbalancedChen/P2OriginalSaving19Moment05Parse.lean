import ImbalancedChen.P2OriginalSaving19Moment05Metadata
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock013
import ImbalancedChen.P2OriginalSaving19ParseFromValue00

/-! Whole original moment05 pure SourceJson parse, assembled from checked compact-input spans. No typed decode claim.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Parsing
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
  err.putStrLn "P26_MOMENT05 whole_before_last_header_binding"
  err.flush

theorem moment_records_header_prefix :
    (momentRest05 348).take 15 = momentRecordsHeaderChars := by rfl

theorem moment_records_header_split :
    momentRest05 348 = momentRecordsHeaderChars ++ momentRest05 363 := by
  calc
    momentRest05 348 =
        (momentRest05 348).take 15 ++ (momentRest05 348).drop 15 :=
      (List.take_append_drop 15 (momentRest05 348)).symm
    _ = momentRecordsHeaderChars ++ (momentRest05 348).drop 15 :=
      congrArg (fun p => p ++ (momentRest05 348).drop 15) moment_records_header_prefix
    _ = momentRecordsHeaderChars ++ momentRest05 363 :=
      congrArg (fun rest => momentRecordsHeaderChars ++ rest) (momentRest05_drop 348 15)

theorem moment_records_separator_prefix :
    (momentRest05 28968).take 3 = momentRecordsSeparatorChars := by rfl

theorem moment_records_separator_split :
    momentRest05 28968 = momentRecordsSeparatorChars ++ momentRest05 28971 := by
  calc
    momentRest05 28968 =
        (momentRest05 28968).take 3 ++ (momentRest05 28968).drop 3 :=
      (List.take_append_drop 3 (momentRest05 28968)).symm
    _ = momentRecordsSeparatorChars ++ (momentRest05 28968).drop 3 :=
      congrArg (fun p => p ++ (momentRest05 28968).drop 3) moment_records_separator_prefix
    _ = momentRecordsSeparatorChars ++ momentRest05 28971 :=
      congrArg (fun rest => momentRecordsSeparatorChars ++ rest) (momentRest05_drop 28968 3)

theorem moment_trailing_prefix :
    (momentRest05 28971).take 2 = momentTrailingChars := by rfl

theorem moment_trailing_split :
    momentRest05 28971 = momentTrailingChars ++ momentRest05 28973 := by
  calc
    momentRest05 28971 =
        (momentRest05 28971).take 2 ++ (momentRest05 28971).drop 2 :=
      (List.take_append_drop 2 (momentRest05 28971)).symm
    _ = momentTrailingChars ++ (momentRest05 28971).drop 2 :=
      congrArg (fun p => p ++ (momentRest05 28971).drop 2) moment_trailing_prefix
    _ = momentTrailingChars ++ momentRest05 28973 :=
      congrArg (fun rest => momentTrailingChars ++ rest) (momentRest05_drop 28971 2)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 whole_after_last_raw_bindings"
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
    SourceJson.object (fuel + 95) (SourceJson.white (momentRest05 348)) momentMetadataAcc009 =
      .ok (momentRootValue, momentRest05 28971) := by
  calc
    SourceJson.object (fuel + 95) (SourceJson.white (momentRest05 348)) momentMetadataAcc009 =
        SourceJson.object (fuel + 95)
          (SourceJson.white (momentRecordsHeaderChars ++ momentRest05 363)) momentMetadataAcc009 :=
      congrArg (fun rest => SourceJson.object (fuel + 95) (SourceJson.white rest) momentMetadataAcc009)
        moment_records_header_split
    _ = (SourceJson.value (fuel + 94) (momentRest05 363)).bind
        (momentRecordsAfterValue (fuel + 94)) :=
      object_moment_records_header fuel (momentRest05 363)
    _ = (Except.ok (momentRecordsArrayValue, momentRest05 28968)).bind
        (momentRecordsAfterValue (fuel + 94)) :=
      congrArg (fun result => result.bind (momentRecordsAfterValue (fuel + 94)))
        (value_moment_records_original fuel)
    _ = (Except.ok (momentRecordsArrayValue,
          momentRecordsSeparatorChars ++ momentRest05 28971)).bind
        (momentRecordsAfterValue (fuel + 94)) :=
      congrArg (fun rest => (Except.ok (momentRecordsArrayValue, rest)).bind
        (momentRecordsAfterValue (fuel + 94))) moment_records_separator_split
    _ = .ok (momentRootValue, momentRest05 28971) :=
      moment_records_after_value_separator fuel (momentRest05 28971)

theorem value_moment05_original (fuel : Nat) :
    SourceJson.value (fuel + 105) momentChars05 =
      .ok (momentRootValue, momentRest05 28971) := by
  exact (momentChars05_through_metadata fuel).trans (object_moment_records_original fuel)

theorem momentTrailing_white : SourceJson.white (momentRest05 28971) = [] := by
  calc
    SourceJson.white (momentRest05 28971) =
        SourceJson.white (momentTrailingChars ++ momentRest05 28973) :=
      congrArg SourceJson.white moment_trailing_split
    _ = SourceJson.white (momentTrailingChars ++ []) :=
      congrArg (fun rest => SourceJson.white (momentTrailingChars ++ rest)) momentRest05_end
    _ = [] := by rfl

theorem momentChars05_parseChars : SourceJson.parseChars momentChars05 = .ok momentRootValue := by
  apply SourceJson.parseChars_of_value_eq (tail := momentRest05 28971)
  · rw [momentChars05_length]
    exact value_moment05_original 28869
  · exact momentTrailing_white

theorem momentPacked05_parseChars :
    SourceJson.parseChars momentPacked05.toList = .ok momentRootValue :=
  momentChars05_parseChars

theorem momentPacked05_parse :
    SourceJson.parse (String.ofList momentPacked05.toList) = .ok momentRootValue :=
  (SourceJson.parse_ofList momentPacked05.toList).trans momentPacked05_parseChars

theorem momentPacked05_parse_success :
    (SourceJson.parse (String.ofList momentPacked05.toList)).toOption.isSome = true := by
  rw [momentPacked05_parse]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 whole_original_parser_complete"
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
#print axioms value_moment05_original
#print axioms momentTrailing_white
#print axioms momentChars05_parseChars
#print axioms momentPacked05_parseChars
#print axioms momentPacked05_parse
#print axioms momentPacked05_parse_success

end ImbalancedChen.P2OriginalSaving19Moment05Parsing
