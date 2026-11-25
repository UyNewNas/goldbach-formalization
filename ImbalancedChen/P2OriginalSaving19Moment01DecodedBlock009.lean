import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock008
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock009

/-! Original typed moment records 36 through 39; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord036 : SourceJson :=
  (momentRecordsChunk036Push []).head (List.cons_ne_nil _ _)

theorem moment_record_036_push_eq (acc : List SourceJson) :
    momentRecordsChunk036Push acc = momentJsonRecord036 :: acc := by rfl

noncomputable def momentTypedRecord036 : MomentRecord :=
  { simplexId := 36,
    factorFloorsQ80 := #[(1954605949272630660062 : Int), (2125636256861745363687 : Int), (271103503694685219885 : Int), (488356164610566374975 : Int), (886293828898694745659 : Int), (1688572644060655090039 : Int), (1244305629640262209596 : Int), (950101642163336474236 : Int), (1166482998390693530957 : Int), (1261705760326453291749 : Int)],
    oldFloorQ96 := (2245334694786144614 : Int),
    newFloorQ96 := (2267802958712428967 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_036_before_decode"
  err.flush

theorem decode_moment_record_036 :
    decodeMomentRecord momentJsonRecord036 = .ok momentTypedRecord036 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_036_decoded"
  err.flush

noncomputable def momentJsonRecord037 : SourceJson :=
  (momentRecordsChunk037Push []).head (List.cons_ne_nil _ _)

theorem moment_record_037_push_eq (acc : List SourceJson) :
    momentRecordsChunk037Push acc = momentJsonRecord037 :: acc := by rfl

noncomputable def momentTypedRecord037 : MomentRecord :=
  { simplexId := 37,
    factorFloorsQ80 := #[(1912240584970937784975 : Int), (2028637403066180302435 : Int), (261332918390604376414 : Int), (491398580462495544161 : Int), (886256935643456327145 : Int), (1688783514747866303148 : Int), (1198809590629039000343 : Int), (919757645113864340320 : Int), (1093927042459800616444 : Int), (1392966624041683116549 : Int)],
    oldFloorQ96 := (3324704930090557271 : Int),
    newFloorQ96 := (3357521191995091358 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_037_before_decode"
  err.flush

theorem decode_moment_record_037 :
    decodeMomentRecord momentJsonRecord037 = .ok momentTypedRecord037 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_037_decoded"
  err.flush

noncomputable def momentJsonRecord038 : SourceJson :=
  (momentRecordsChunk038Push []).head (List.cons_ne_nil _ _)

theorem moment_record_038_push_eq (acc : List SourceJson) :
    momentRecordsChunk038Push acc = momentJsonRecord038 :: acc := by rfl

noncomputable def momentTypedRecord038 : MomentRecord :=
  { simplexId := 38,
    factorFloorsQ80 := #[(1842246141081672734523 : Int), (1985776473574055902711 : Int), (261333053429207452635 : Int), (484559818868031512345 : Int), (911033663973169596039 : Int), (1765334396410399080654 : Int), (1205331142151405348664 : Int), (931958380358930349924 : Int), (1014326895471684236581 : Int), (1636892063179486165732 : Int)],
    oldFloorQ96 := (5392919005722065680 : Int),
    newFloorQ96 := (5446891357346563042 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_038_before_decode"
  err.flush

theorem decode_moment_record_038 :
    decodeMomentRecord momentJsonRecord038 = .ok momentTypedRecord038 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_038_decoded"
  err.flush

noncomputable def momentJsonRecord039 : SourceJson :=
  (momentRecordsChunk039Push []).head (List.cons_ne_nil _ _)

theorem moment_record_039_push_eq (acc : List SourceJson) :
    momentRecordsChunk039Push acc = momentJsonRecord039 :: acc := by rfl

noncomputable def momentTypedRecord039 : MomentRecord :=
  { simplexId := 39,
    factorFloorsQ80 := #[(2441726523832743371028 : Int), (2585180211744802706191 : Int), (283516380575893683959 : Int), (613032931581331705116 : Int), (988550112649950104952 : Int), (2010304308593712393869 : Int), (1428689429409220360897 : Int), (1157161530721762573842 : Int), (1309767252763055863842 : Int), (1309822923261870419284 : Int)],
    oldFloorQ96 := (44265334701173 : Int),
    newFloorQ96 := (44785662727479 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_039_before_decode"
  err.flush

theorem decode_moment_record_039 :
    decodeMomentRecord momentJsonRecord039 = .ok momentTypedRecord039 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_039_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock009 : List SourceJson := [momentJsonRecord036, momentJsonRecord037, momentJsonRecord038, momentJsonRecord039]
noncomputable def momentTypedRecordsBlock009 : List MomentRecord := [momentTypedRecord036, momentTypedRecord037, momentTypedRecord038, momentTypedRecord039]

theorem moment_records_block_009_push_eq (acc : List SourceJson) :
    momentRecordsBlock009Push acc = [momentJsonRecord039, momentJsonRecord038, momentJsonRecord037, momentJsonRecord036] ++ acc := by rfl

theorem moment_records_block_009_reverse (acc : List SourceJson) :
    (momentRecordsBlock009Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock009 := by
  rw [moment_records_block_009_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_009 :
    momentJsonRecordsBlock009.mapM decodeMomentRecord = .ok momentTypedRecordsBlock009 := by
  simp only [momentJsonRecordsBlock009, momentTypedRecordsBlock009, List.mapM_cons, List.mapM_nil,
    decode_moment_record_036, decode_moment_record_037, decode_moment_record_038, decode_moment_record_039]
  rfl

noncomputable def momentTypedRowsThroughBlock009 : List MomentRecord := momentTypedRowsThroughBlock008 ++ momentTypedRecordsBlock009

theorem decode_moment_records_through_block_009 :
    momentRecordsAcc040.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock009 := by
  change (momentRecordsBlock009Push momentRecordsAcc036).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_009_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_008, decode_moment_records_block_009]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_009_complete"
  err.flush

#print axioms moment_record_036_push_eq
#print axioms decode_moment_record_036
#print axioms moment_record_037_push_eq
#print axioms decode_moment_record_037
#print axioms moment_record_038_push_eq
#print axioms decode_moment_record_038
#print axioms moment_record_039_push_eq
#print axioms decode_moment_record_039
#print axioms moment_records_block_009_push_eq
#print axioms moment_records_block_009_reverse
#print axioms decode_moment_records_block_009
#print axioms decode_moment_records_through_block_009

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
