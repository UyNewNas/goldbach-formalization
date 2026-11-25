import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock019
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock020

/-! Original typed moment records 80 through 83; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord080 : SourceJson :=
  (momentRecordsChunk080Push []).head (List.cons_ne_nil _ _)

theorem moment_record_080_push_eq (acc : List SourceJson) :
    momentRecordsChunk080Push acc = momentJsonRecord080 :: acc := by rfl

noncomputable def momentTypedRecord080 : MomentRecord :=
  { simplexId := 80,
    factorFloorsQ80 := #[(656194257133892233964 : Int), (690988885080637210821 : Int), (299360752949400424748 : Int), (491735250682458195782 : Int), (1244736356760241484437 : Int), (2105347394866542589491 : Int), (1842955031581105095210 : Int), (953645940422552474893 : Int), (987729111799978440378 : Int), (1061610251199950076152 : Int)],
    oldFloorQ96 := (23380824562307476258 : Int),
    newFloorQ96 := (23581548389536814846 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_080_before_decode"
  err.flush

theorem decode_moment_record_080 :
    decodeMomentRecord momentJsonRecord080 = .ok momentTypedRecord080 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_080_decoded"
  err.flush

noncomputable def momentJsonRecord081 : SourceJson :=
  (momentRecordsChunk081Push []).head (List.cons_ne_nil _ _)

theorem moment_record_081_push_eq (acc : List SourceJson) :
    momentRecordsChunk081Push acc = momentJsonRecord081 :: acc := by rfl

noncomputable def momentTypedRecord081 : MomentRecord :=
  { simplexId := 81,
    factorFloorsQ80 := #[(656194020670705843830 : Int), (690989286391783020373 : Int), (299360843885714849476 : Int), (491734946214170182575 : Int), (1244736011192405705120 : Int), (2105348284445505902621 : Int), (2397958505418823985371 : Int), (987715119330258040452 : Int), (987702272331057182205 : Int), (1061614203140302414935 : Int)],
    oldFloorQ96 := (1274304094614762 : Int),
    newFloorQ96 := (1285870354073000 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_081_before_decode"
  err.flush

theorem decode_moment_record_081 :
    decodeMomentRecord momentJsonRecord081 = .ok momentTypedRecord081 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_081_decoded"
  err.flush

noncomputable def momentJsonRecord082 : SourceJson :=
  (momentRecordsChunk082Push []).head (List.cons_ne_nil _ _)

theorem moment_record_082_push_eq (acc : List SourceJson) :
    momentRecordsChunk082Push acc = momentJsonRecord082 :: acc := by rfl

noncomputable def momentTypedRecord082 : MomentRecord :=
  { simplexId := 82,
    factorFloorsQ80 := #[(1110310982284981229384 : Int), (1152062587548881561079 : Int), (321620098221330254662 : Int), (655549816870706769509 : Int), (1351797015168729964520 : Int), (2340531744745944473976 : Int), (1372464243924112220915 : Int), (1052462039435169767386 : Int), (1160086615122040754544 : Int), (1160137497264055970428 : Int)],
    oldFloorQ96 := (186157617241858 : Int),
    newFloorQ96 := (187964426799765 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_082_before_decode"
  err.flush

theorem decode_moment_record_082 :
    decodeMomentRecord momentJsonRecord082 = .ok momentTypedRecord082 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_082_decoded"
  err.flush

noncomputable def momentJsonRecord083 : SourceJson :=
  (momentRecordsChunk083Push []).head (List.cons_ne_nil _ _)

theorem moment_record_083_push_eq (acc : List SourceJson) :
    momentRecordsChunk083Push acc = momentJsonRecord083 :: acc := by rfl

noncomputable def momentTypedRecord083 : MomentRecord :=
  { simplexId := 83,
    factorFloorsQ80 := #[(1013431191089166357098 : Int), (1081675402846458250469 : Int), (306290814411077450941 : Int), (564285492419653002238 : Int), (1370789544790985990859 : Int), (1974869239812719114593 : Int), (1341581779594279957750 : Int), (1025704203943480530827 : Int), (1142015561434929796065 : Int), (1216479263444552232699 : Int)],
    oldFloorQ96 := (2057112141502622274 : Int),
    newFloorQ96 := (2075978937748630764 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_083_before_decode"
  err.flush

theorem decode_moment_record_083 :
    decodeMomentRecord momentJsonRecord083 = .ok momentTypedRecord083 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_083_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock020 : List SourceJson := [momentJsonRecord080, momentJsonRecord081, momentJsonRecord082, momentJsonRecord083]
noncomputable def momentTypedRecordsBlock020 : List MomentRecord := [momentTypedRecord080, momentTypedRecord081, momentTypedRecord082, momentTypedRecord083]

theorem moment_records_block_020_push_eq (acc : List SourceJson) :
    momentRecordsBlock020Push acc = [momentJsonRecord083, momentJsonRecord082, momentJsonRecord081, momentJsonRecord080] ++ acc := by rfl

theorem moment_records_block_020_reverse (acc : List SourceJson) :
    (momentRecordsBlock020Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock020 := by
  rw [moment_records_block_020_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_020 :
    momentJsonRecordsBlock020.mapM decodeMomentRecord = .ok momentTypedRecordsBlock020 := by
  simp only [momentJsonRecordsBlock020, momentTypedRecordsBlock020, List.mapM_cons, List.mapM_nil,
    decode_moment_record_080, decode_moment_record_081, decode_moment_record_082, decode_moment_record_083]
  rfl

noncomputable def momentTypedRowsThroughBlock020 : List MomentRecord := momentTypedRowsThroughBlock019 ++ momentTypedRecordsBlock020

theorem decode_moment_records_through_block_020 :
    momentRecordsAcc084.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock020 := by
  change (momentRecordsBlock020Push momentRecordsAcc080).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_020_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_019, decode_moment_records_block_020]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_020_complete"
  err.flush

#print axioms moment_record_080_push_eq
#print axioms decode_moment_record_080
#print axioms moment_record_081_push_eq
#print axioms decode_moment_record_081
#print axioms moment_record_082_push_eq
#print axioms decode_moment_record_082
#print axioms moment_record_083_push_eq
#print axioms decode_moment_record_083
#print axioms moment_records_block_020_push_eq
#print axioms moment_records_block_020_reverse
#print axioms decode_moment_records_block_020
#print axioms decode_moment_records_through_block_020

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
