import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock034
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock035

/-! Original typed moment records 140 through 143; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord140 : SourceJson :=
  (momentRecordsChunk140Push []).head (List.cons_ne_nil _ _)

theorem moment_record_140_push_eq (acc : List SourceJson) :
    momentRecordsChunk140Push acc = momentJsonRecord140 :: acc := by rfl

noncomputable def momentTypedRecord140 : MomentRecord :=
  { simplexId := 140,
    factorFloorsQ80 := #[(674307306441995954667 : Int), (664093371098900721000 : Int), (103969860501125655569 : Int), (562834407126120200593 : Int), (458521695896370693677 : Int), (968039595363778167514 : Int), (797185332015298690662 : Int), (727733566336161651764 : Int), (686896139080127058069 : Int), (664707705194229246099 : Int)],
    oldFloorQ96 := (248018074521301 : Int),
    newFloorQ96 := (249315638686878 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_140_before_decode"
  err.flush

theorem decode_moment_record_140 :
    decodeMomentRecord momentJsonRecord140 = .ok momentTypedRecord140 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_140_decoded"
  err.flush

noncomputable def momentJsonRecord141 : SourceJson :=
  (momentRecordsChunk141Push []).head (List.cons_ne_nil _ _)

theorem moment_record_141_push_eq (acc : List SourceJson) :
    momentRecordsChunk141Push acc = momentJsonRecord141 :: acc := by rfl

noncomputable def momentTypedRecord141 : MomentRecord :=
  { simplexId := 141,
    factorFloorsQ80 := #[(672337837952507231173 : Int), (660170503855431596453 : Int), (108412190595848712000 : Int), (543404654930277521102 : Int), (446830369687403265313 : Int), (1021234131748565315984 : Int), (837490268840867084735 : Int), (685290192022083167705 : Int), (685288238466155755090 : Int), (746641209763168920380 : Int)],
    oldFloorQ96 := (260132982826 : Int),
    newFloorQ96 := (261515302826 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_141_before_decode"
  err.flush

theorem decode_moment_record_141 :
    decodeMomentRecord momentJsonRecord141 = .ok momentTypedRecord141 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_141_decoded"
  err.flush

noncomputable def momentJsonRecord142 : SourceJson :=
  (momentRecordsChunk142Push []).head (List.cons_ne_nil _ _)

theorem moment_record_142_push_eq (acc : List SourceJson) :
    momentRecordsChunk142Push acc = momentJsonRecord142 :: acc := by rfl

noncomputable def momentTypedRecord142 : MomentRecord :=
  { simplexId := 142,
    factorFloorsQ80 := #[(678212600329657368059 : Int), (668127210750489258495 : Int), (98346356919437710631 : Int), (559210496984801535066 : Int), (554910547936314582563 : Int), (963884713932521074767 : Int), (800675587258797097273 : Int), (733663380129716897249 : Int), (681927494984498765060 : Int), (681982406408451928079 : Int)],
    oldFloorQ96 := (41392539793 : Int),
    newFloorQ96 := (41612971937 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_142_before_decode"
  err.flush

theorem decode_moment_record_142 :
    decodeMomentRecord momentJsonRecord142 = .ok momentTypedRecord142 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_142_decoded"
  err.flush

noncomputable def momentJsonRecord143 : SourceJson :=
  (momentRecordsChunk143Push []).head (List.cons_ne_nil _ _)

theorem moment_record_143_push_eq (acc : List SourceJson) :
    momentRecordsChunk143Push acc = momentJsonRecord143 :: acc := by rfl

noncomputable def momentTypedRecord143 : MomentRecord :=
  { simplexId := 143,
    factorFloorsQ80 := #[(890794312325491750893 : Int), (885555663396304661638 : Int), (100260632354101144053 : Int), (557056663040711344995 : Int), (658821706754689648637 : Int), (988537750962855358933 : Int), (806592850442211784159 : Int), (732302722830699606140 : Int), (672679937735992411261 : Int), (672740123304551059812 : Int)],
    oldFloorQ96 := (42442986841 : Int),
    newFloorQ96 := (42688232012 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_143_before_decode"
  err.flush

theorem decode_moment_record_143 :
    decodeMomentRecord momentJsonRecord143 = .ok momentTypedRecord143 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_143_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock035 : List SourceJson := [momentJsonRecord140, momentJsonRecord141, momentJsonRecord142, momentJsonRecord143]
noncomputable def momentTypedRecordsBlock035 : List MomentRecord := [momentTypedRecord140, momentTypedRecord141, momentTypedRecord142, momentTypedRecord143]

theorem moment_records_block_035_push_eq (acc : List SourceJson) :
    momentRecordsBlock035Push acc = [momentJsonRecord143, momentJsonRecord142, momentJsonRecord141, momentJsonRecord140] ++ acc := by rfl

theorem moment_records_block_035_reverse (acc : List SourceJson) :
    (momentRecordsBlock035Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock035 := by
  rw [moment_records_block_035_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_035 :
    momentJsonRecordsBlock035.mapM decodeMomentRecord = .ok momentTypedRecordsBlock035 := by
  simp only [momentJsonRecordsBlock035, momentTypedRecordsBlock035, List.mapM_cons, List.mapM_nil,
    decode_moment_record_140, decode_moment_record_141, decode_moment_record_142, decode_moment_record_143]
  rfl

noncomputable def momentTypedRowsThroughBlock035 : List MomentRecord := momentTypedRowsThroughBlock034 ++ momentTypedRecordsBlock035

theorem decode_moment_records_through_block_035 :
    momentRecordsAcc144.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock035 := by
  change (momentRecordsBlock035Push momentRecordsAcc140).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_035_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_034, decode_moment_records_block_035]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_035_complete"
  err.flush

#print axioms moment_record_140_push_eq
#print axioms decode_moment_record_140
#print axioms moment_record_141_push_eq
#print axioms decode_moment_record_141
#print axioms moment_record_142_push_eq
#print axioms decode_moment_record_142
#print axioms moment_record_143_push_eq
#print axioms decode_moment_record_143
#print axioms moment_records_block_035_push_eq
#print axioms moment_records_block_035_reverse
#print axioms decode_moment_records_block_035
#print axioms decode_moment_records_through_block_035

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
