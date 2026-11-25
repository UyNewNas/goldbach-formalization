import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock025
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock026

/-! Original typed moment records 104 through 107; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord104 : SourceJson :=
  (momentRecordsChunk104Push []).head (List.cons_ne_nil _ _)

theorem moment_record_104_push_eq (acc : List SourceJson) :
    momentRecordsChunk104Push acc = momentJsonRecord104 :: acc := by rfl

noncomputable def momentTypedRecord104 : MomentRecord :=
  { simplexId := 104,
    factorFloorsQ80 := #[(1731046614250239858392 : Int), (1673541489000752349399 : Int), (234187429447724545935 : Int), (697595768025378620925 : Int), (1105165802599453665374 : Int), (2004463047589914109307 : Int), (1443886656162321238530 : Int), (1083895556033594543351 : Int), (1083880929561605040502 : Int), (1941139674028865297023 : Int)],
    oldFloorQ96 := (9750895975463 : Int),
    newFloorQ96 := (9856306784248 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_104_before_decode"
  err.flush

theorem decode_moment_record_104 :
    decodeMomentRecord momentJsonRecord104 = .ok momentTypedRecord104 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_104_decoded"
  err.flush

noncomputable def momentJsonRecord105 : SourceJson :=
  (momentRecordsChunk105Push []).head (List.cons_ne_nil _ _)

theorem moment_record_105_push_eq (acc : List SourceJson) :
    momentRecordsChunk105Push acc = momentJsonRecord105 :: acc := by rfl

noncomputable def momentTypedRecord105 : MomentRecord :=
  { simplexId := 105,
    factorFloorsQ80 := #[(1815865926695117492430 : Int), (1763636454707914336399 : Int), (219258562822750312732 : Int), (759264161025109454687 : Int), (1040287830614637490791 : Int), (2014778823589684716316 : Int), (1432784082788074528663 : Int), (1125703369120106128401 : Int), (1125692005603374696728 : Int), (1702917832559124624808 : Int)],
    oldFloorQ96 := (3248242495042 : Int),
    newFloorQ96 := (3283360967917 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_105_before_decode"
  err.flush

theorem decode_moment_record_105 :
    decodeMomentRecord momentJsonRecord105 = .ok momentTypedRecord105 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_105_decoded"
  err.flush

noncomputable def momentJsonRecord106 : SourceJson :=
  (momentRecordsChunk106Push []).head (List.cons_ne_nil _ _)

theorem moment_record_106_push_eq (acc : List SourceJson) :
    momentRecordsChunk106Push acc = momentJsonRecord106 :: acc := by rfl

noncomputable def momentTypedRecord106 : MomentRecord :=
  { simplexId := 106,
    factorFloorsQ80 := #[(1308202667718963614202 : Int), (1268559076458308309009 : Int), (164828341369507416433 : Int), (706743346798636338392 : Int), (801249543430565728069 : Int), (1584537615411523837918 : Int), (1171871794591752566060 : Int), (937154591565609369531 : Int), (937147643862502000257 : Int), (1593373558675639701719 : Int)],
    oldFloorQ96 := (404325039914 : Int),
    newFloorQ96 := (407843174282 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_106_before_decode"
  err.flush

theorem decode_moment_record_106 :
    decodeMomentRecord momentJsonRecord106 = .ok momentTypedRecord106 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_106_decoded"
  err.flush

noncomputable def momentJsonRecord107 : SourceJson :=
  (momentRecordsChunk107Push []).head (List.cons_ne_nil _ _)

theorem moment_record_107_push_eq (acc : List SourceJson) :
    momentRecordsChunk107Push acc = momentJsonRecord107 :: acc := by rfl

noncomputable def momentTypedRecord107 : MomentRecord :=
  { simplexId := 107,
    factorFloorsQ80 := #[(662173419172697945664 : Int), (679377514873701424996 : Int), (347142875757740126851 : Int), (557639027976038704330 : Int), (2100988917274616043386 : Int), (2587376406515301630502 : Int), (1937095878312312463472 : Int), (913155049130358222573 : Int), (802818118672734684755 : Int), (802844109025506271443 : Int)],
    oldFloorQ96 := (946765566677643 : Int),
    newFloorQ96 := (955728236689438 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_107_before_decode"
  err.flush

theorem decode_moment_record_107 :
    decodeMomentRecord momentJsonRecord107 = .ok momentTypedRecord107 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_107_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock026 : List SourceJson := [momentJsonRecord104, momentJsonRecord105, momentJsonRecord106, momentJsonRecord107]
noncomputable def momentTypedRecordsBlock026 : List MomentRecord := [momentTypedRecord104, momentTypedRecord105, momentTypedRecord106, momentTypedRecord107]

theorem moment_records_block_026_push_eq (acc : List SourceJson) :
    momentRecordsBlock026Push acc = [momentJsonRecord107, momentJsonRecord106, momentJsonRecord105, momentJsonRecord104] ++ acc := by rfl

theorem moment_records_block_026_reverse (acc : List SourceJson) :
    (momentRecordsBlock026Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock026 := by
  rw [moment_records_block_026_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_026 :
    momentJsonRecordsBlock026.mapM decodeMomentRecord = .ok momentTypedRecordsBlock026 := by
  simp only [momentJsonRecordsBlock026, momentTypedRecordsBlock026, List.mapM_cons, List.mapM_nil,
    decode_moment_record_104, decode_moment_record_105, decode_moment_record_106, decode_moment_record_107]
  rfl

noncomputable def momentTypedRowsThroughBlock026 : List MomentRecord := momentTypedRowsThroughBlock025 ++ momentTypedRecordsBlock026

theorem decode_moment_records_through_block_026 :
    momentRecordsAcc108.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock026 := by
  change (momentRecordsBlock026Push momentRecordsAcc104).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_026_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_025, decode_moment_records_block_026]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_026_complete"
  err.flush

#print axioms moment_record_104_push_eq
#print axioms decode_moment_record_104
#print axioms moment_record_105_push_eq
#print axioms decode_moment_record_105
#print axioms moment_record_106_push_eq
#print axioms decode_moment_record_106
#print axioms moment_record_107_push_eq
#print axioms decode_moment_record_107
#print axioms moment_records_block_026_push_eq
#print axioms moment_records_block_026_reverse
#print axioms decode_moment_records_block_026
#print axioms decode_moment_records_through_block_026

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
