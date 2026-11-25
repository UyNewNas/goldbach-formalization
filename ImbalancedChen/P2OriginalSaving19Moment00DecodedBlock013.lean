import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock012
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock013

/-! Original typed moment records 52 through 55; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord052 : SourceJson :=
  (momentRecordsChunk052Push []).head (List.cons_ne_nil _ _)

theorem moment_record_052_push_eq (acc : List SourceJson) :
    momentRecordsChunk052Push acc = momentJsonRecord052 :: acc := by rfl

noncomputable def momentTypedRecord052 : MomentRecord :=
  { simplexId := 52,
    factorFloorsQ80 := #[(394096344133902776793 : Int), (455621947397685018200 : Int), (217731390809947309929 : Int), (442048052431282212309 : Int), (315351126359528458893 : Int), (484388604561348714051 : Int), (331610572586695681550 : Int), (418406407692514578171 : Int), (299701501587412628129 : Int), (299714559696473170588 : Int)],
    oldFloorQ96 := (2771638440812 : Int),
    newFloorQ96 := (2780039181091 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_052_before_decode"
  err.flush

theorem decode_moment_record_052 :
    decodeMomentRecord momentJsonRecord052 = .ok momentTypedRecord052 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_052_decoded"
  err.flush

noncomputable def momentJsonRecord053 : SourceJson :=
  (momentRecordsChunk053Push []).head (List.cons_ne_nil _ _)

theorem moment_record_053_push_eq (acc : List SourceJson) :
    momentRecordsChunk053Push acc = momentJsonRecord053 :: acc := by rfl

noncomputable def momentTypedRecord053 : MomentRecord :=
  { simplexId := 53,
    factorFloorsQ80 := #[(344912006650559990834 : Int), (418682565246230446933 : Int), (187841618015548608986 : Int), (339588229938707663198 : Int), (294660566897716219440 : Int), (425727391515427995814 : Int), (335457539352479229386 : Int), (356063763046814857516 : Int), (289981533674247521698 : Int), (289992053725503797364 : Int)],
    oldFloorQ96 := (2774675913293 : Int),
    newFloorQ96 := (2782220944410 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_053_before_decode"
  err.flush

theorem decode_moment_record_053 :
    decodeMomentRecord momentJsonRecord053 = .ok momentTypedRecord053 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_053_decoded"
  err.flush

noncomputable def momentJsonRecord054 : SourceJson :=
  (momentRecordsChunk054Push []).head (List.cons_ne_nil _ _)

theorem moment_record_054_push_eq (acc : List SourceJson) :
    momentRecordsChunk054Push acc = momentJsonRecord054 :: acc := by rfl

noncomputable def momentTypedRecord054 : MomentRecord :=
  { simplexId := 54,
    factorFloorsQ80 := #[(193243107298541830362 : Int), (280377254751484612496 : Int), (129409204641365702802 : Int), (141587296363254629585 : Int), (204316516597626103947 : Int), (193685076401687737793 : Int), (317276676634302997154 : Int), (311198583701919868452 : Int), (194383010569840757831 : Int), (194389551102545439445 : Int)],
    oldFloorQ96 := (2358468210131 : Int),
    newFloorQ96 := (2362685614565 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_054_before_decode"
  err.flush

theorem decode_moment_record_054 :
    decodeMomentRecord momentJsonRecord054 = .ok momentTypedRecord054 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_054_decoded"
  err.flush

noncomputable def momentJsonRecord055 : SourceJson :=
  (momentRecordsChunk055Push []).head (List.cons_ne_nil _ _)

theorem moment_record_055_push_eq (acc : List SourceJson) :
    momentRecordsChunk055Push acc = momentJsonRecord055 :: acc := by rfl

noncomputable def momentTypedRecord055 : MomentRecord :=
  { simplexId := 55,
    factorFloorsQ80 := #[(162952307881926921989 : Int), (174636694318090938463 : Int), (222256855541097220215 : Int), (580319622242671930292 : Int), (256091853335053281144 : Int), (549453281279551238132 : Int), (688504111432906453896 : Int), (475567272041068538173 : Int), (323435937327124139809 : Int), (323461533263457575533 : Int)],
    oldFloorQ96 := (6789578685666 : Int),
    newFloorQ96 := (6810709793337 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_055_before_decode"
  err.flush

theorem decode_moment_record_055 :
    decodeMomentRecord momentJsonRecord055 = .ok momentTypedRecord055 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_055_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock013 : List SourceJson := [momentJsonRecord052, momentJsonRecord053, momentJsonRecord054, momentJsonRecord055]
noncomputable def momentTypedRecordsBlock013 : List MomentRecord := [momentTypedRecord052, momentTypedRecord053, momentTypedRecord054, momentTypedRecord055]

theorem moment_records_block_013_push_eq (acc : List SourceJson) :
    momentRecordsBlock013Push acc = [momentJsonRecord055, momentJsonRecord054, momentJsonRecord053, momentJsonRecord052] ++ acc := by rfl

theorem moment_records_block_013_reverse (acc : List SourceJson) :
    (momentRecordsBlock013Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock013 := by
  rw [moment_records_block_013_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_013 :
    momentJsonRecordsBlock013.mapM decodeMomentRecord = .ok momentTypedRecordsBlock013 := by
  simp only [momentJsonRecordsBlock013, momentTypedRecordsBlock013, List.mapM_cons, List.mapM_nil,
    decode_moment_record_052, decode_moment_record_053, decode_moment_record_054, decode_moment_record_055]
  rfl

noncomputable def momentTypedRowsThroughBlock013 : List MomentRecord := momentTypedRowsThroughBlock012 ++ momentTypedRecordsBlock013

theorem decode_moment_records_through_block_013 :
    momentRecordsAcc056.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock013 := by
  change (momentRecordsBlock013Push momentRecordsAcc052).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_013_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_012, decode_moment_records_block_013]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_block_013_complete"
  err.flush

#print axioms moment_record_052_push_eq
#print axioms decode_moment_record_052
#print axioms moment_record_053_push_eq
#print axioms decode_moment_record_053
#print axioms moment_record_054_push_eq
#print axioms decode_moment_record_054
#print axioms moment_record_055_push_eq
#print axioms decode_moment_record_055
#print axioms moment_records_block_013_push_eq
#print axioms moment_records_block_013_reverse
#print axioms decode_moment_records_block_013
#print axioms decode_moment_records_through_block_013

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
