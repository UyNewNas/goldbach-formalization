import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock016
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock017

/-! Original typed moment records 68 through 71; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord068 : SourceJson :=
  (momentRecordsChunk068Push []).head (List.cons_ne_nil _ _)

theorem moment_record_068_push_eq (acc : List SourceJson) :
    momentRecordsChunk068Push acc = momentJsonRecord068 :: acc := by rfl

noncomputable def momentTypedRecord068 : MomentRecord :=
  { simplexId := 68,
    factorFloorsQ80 := #[(3096115400926500386505 : Int), (3402045168891273481021 : Int), (258164208717387105594 : Int), (623234645713732108520 : Int), (1579852407659806878498 : Int), (1839563665927144943883 : Int), (1445215910163064438463 : Int), (1231550462782988897685 : Int), (1322836018540229004533 : Int), (1322891386576716243981 : Int)],
    oldFloorQ96 := (11018138262332 : Int),
    newFloorQ96 := (11166053221519 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_068_before_decode"
  err.flush

theorem decode_moment_record_068 :
    decodeMomentRecord momentJsonRecord068 = .ok momentTypedRecord068 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_068_decoded"
  err.flush

noncomputable def momentJsonRecord069 : SourceJson :=
  (momentRecordsChunk069Push []).head (List.cons_ne_nil _ _)

theorem moment_record_069_push_eq (acc : List SourceJson) :
    momentRecordsChunk069Push acc = momentJsonRecord069 :: acc := by rfl

noncomputable def momentTypedRecord069 : MomentRecord :=
  { simplexId := 69,
    factorFloorsQ80 := #[(2468091904390094219449 : Int), (2446333834350139395697 : Int), (193061236865355829895 : Int), (692291939913915944388 : Int), (1792884938772301810297 : Int), (1860176920389845776763 : Int), (1243385862062745831073 : Int), (1103085140335284706709 : Int), (971641227622787265442 : Int), (971710517040954369436 : Int)],
    oldFloorQ96 := (305831327963 : Int),
    newFloorQ96 := (309327751214 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_069_before_decode"
  err.flush

theorem decode_moment_record_069 :
    decodeMomentRecord momentJsonRecord069 = .ok momentTypedRecord069 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_069_decoded"
  err.flush

noncomputable def momentJsonRecord070 : SourceJson :=
  (momentRecordsChunk070Push []).head (List.cons_ne_nil _ _)

theorem moment_record_070_push_eq (acc : List SourceJson) :
    momentRecordsChunk070Push acc = momentJsonRecord070 :: acc := by rfl

noncomputable def momentTypedRecord070 : MomentRecord :=
  { simplexId := 70,
    factorFloorsQ80 := #[(1404878842259018653745 : Int), (1408111687790012430983 : Int), (121894955645238234378 : Int), (638176186763074146517 : Int), (1803097653481027265709 : Int), (1258245713372214756544 : Int), (981997139864692630548 : Int), (870954413281426663824 : Int), (771432549536963969886 : Int), (771505869487247524750 : Int)],
    oldFloorQ96 := (38740063893 : Int),
    newFloorQ96 := (39062822077 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_070_before_decode"
  err.flush

theorem decode_moment_record_070 :
    decodeMomentRecord momentJsonRecord070 = .ok momentTypedRecord070 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_070_decoded"
  err.flush

noncomputable def momentJsonRecord071 : SourceJson :=
  (momentRecordsChunk071Push []).head (List.cons_ne_nil _ _)

theorem moment_record_071_push_eq (acc : List SourceJson) :
    momentRecordsChunk071Push acc = momentJsonRecord071 :: acc := by rfl

noncomputable def momentTypedRecord071 : MomentRecord :=
  { simplexId := 71,
    factorFloorsQ80 := #[(1077648185886184845728 : Int), (1072469276239798311480 : Int), (124333659973152139664 : Int), (587903305981126677902 : Int), (1202929027066932403174 : Int), (1198973602725608215845 : Int), (879002875793426391815 : Int), (780879934132820194375 : Int), (744276927721177997763 : Int), (759590119154027387849 : Int)],
    oldFloorQ96 := (918248714516408 : Int),
    newFloorQ96 := (924672636693502 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_071_before_decode"
  err.flush

theorem decode_moment_record_071 :
    decodeMomentRecord momentJsonRecord071 = .ok momentTypedRecord071 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_071_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock017 : List SourceJson := [momentJsonRecord068, momentJsonRecord069, momentJsonRecord070, momentJsonRecord071]
noncomputable def momentTypedRecordsBlock017 : List MomentRecord := [momentTypedRecord068, momentTypedRecord069, momentTypedRecord070, momentTypedRecord071]

theorem moment_records_block_017_push_eq (acc : List SourceJson) :
    momentRecordsBlock017Push acc = [momentJsonRecord071, momentJsonRecord070, momentJsonRecord069, momentJsonRecord068] ++ acc := by rfl

theorem moment_records_block_017_reverse (acc : List SourceJson) :
    (momentRecordsBlock017Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock017 := by
  rw [moment_records_block_017_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_017 :
    momentJsonRecordsBlock017.mapM decodeMomentRecord = .ok momentTypedRecordsBlock017 := by
  simp only [momentJsonRecordsBlock017, momentTypedRecordsBlock017, List.mapM_cons, List.mapM_nil,
    decode_moment_record_068, decode_moment_record_069, decode_moment_record_070, decode_moment_record_071]
  rfl

noncomputable def momentTypedRowsThroughBlock017 : List MomentRecord := momentTypedRowsThroughBlock016 ++ momentTypedRecordsBlock017

theorem decode_moment_records_through_block_017 :
    momentRecordsAcc072.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock017 := by
  change (momentRecordsBlock017Push momentRecordsAcc068).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_017_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_016, decode_moment_records_block_017]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_017_complete"
  err.flush

#print axioms moment_record_068_push_eq
#print axioms decode_moment_record_068
#print axioms moment_record_069_push_eq
#print axioms decode_moment_record_069
#print axioms moment_record_070_push_eq
#print axioms decode_moment_record_070
#print axioms moment_record_071_push_eq
#print axioms decode_moment_record_071
#print axioms moment_records_block_017_push_eq
#print axioms moment_records_block_017_reverse
#print axioms decode_moment_records_block_017
#print axioms decode_moment_records_through_block_017

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
