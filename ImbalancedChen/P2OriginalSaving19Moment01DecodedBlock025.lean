import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock024
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock025

/-! Original typed moment records 100 through 103; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord100 : SourceJson :=
  (momentRecordsChunk100Push []).head (List.cons_ne_nil _ _)

theorem moment_record_100_push_eq (acc : List SourceJson) :
    momentRecordsChunk100Push acc = momentJsonRecord100 :: acc := by rfl

noncomputable def momentTypedRecord100 : MomentRecord :=
  { simplexId := 100,
    factorFloorsQ80 := #[(1815875283938652093698 : Int), (1763645881408716120782 : Int), (219258371728009583538 : Int), (759267487400595918061 : Int), (1040290158812574715308 : Int), (2014778332597326109668 : Int), (1343629514048770895912 : Int), (1190172885680582200682 : Int), (1125691407583220604316 : Int), (1702936323116120115493 : Int)],
    oldFloorQ96 := (13008030052999413 : Int),
    newFloorQ96 := (13148398740129639 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_100_before_decode"
  err.flush

theorem decode_moment_record_100 :
    decodeMomentRecord momentJsonRecord100 = .ok momentTypedRecord100 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_100_decoded"
  err.flush

noncomputable def momentJsonRecord101 : SourceJson :=
  (momentRecordsChunk101Push []).head (List.cons_ne_nil _ _)

theorem moment_record_101_push_eq (acc : List SourceJson) :
    momentRecordsChunk101Push acc = momentJsonRecord101 :: acc := by rfl

noncomputable def momentTypedRecord101 : MomentRecord :=
  { simplexId := 101,
    factorFloorsQ80 := #[(1308209804292982213878 : Int), (1268566312979400540572 : Int), (164828051325730688724 : Int), (706746893422363225946 : Int), (801250833704651813029 : Int), (1584535683269454374040 : Int), (1100866034961103977548 : Int), (983445991853205189806 : Int), (937147278251781048155 : Int), (1593390521466616929255 : Int)],
    oldFloorQ96 := (1619184582916393 : Int),
    newFloorQ96 := (1633240173545782 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_101_before_decode"
  err.flush

theorem decode_moment_record_101 :
    decodeMomentRecord momentJsonRecord101 = .ok momentTypedRecord101 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_101_decoded"
  err.flush

noncomputable def momentJsonRecord102 : SourceJson :=
  (momentRecordsChunk102Push []).head (List.cons_ne_nil _ _)

theorem moment_record_102_push_eq (acc : List SourceJson) :
    momentRecordsChunk102Push acc = momentJsonRecord102 :: acc := by rfl

noncomputable def momentTypedRecord102 : MomentRecord :=
  { simplexId := 102,
    factorFloorsQ80 := #[(1022267631537448173749 : Int), (1087160719213496060735 : Int), (295788799874263011392 : Int), (559987866413828651322 : Int), (1317768241350020926907 : Int), (2060633889791682892600 : Int), (2087571013183685052488 : Int), (1056125035726347470730 : Int), (1056088802781326720171 : Int), (1564101266879704347490 : Int)],
    oldFloorQ96 := (1232579788013199 : Int),
    newFloorQ96 := (1244986199162403 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_102_before_decode"
  err.flush

theorem decode_moment_record_102 :
    decodeMomentRecord momentJsonRecord102 = .ok momentTypedRecord102 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_102_decoded"
  err.flush

noncomputable def momentJsonRecord103 : SourceJson :=
  (momentRecordsChunk103Push []).head (List.cons_ne_nil _ _)

theorem moment_record_103_push_eq (acc : List SourceJson) :
    momentRecordsChunk103Push acc = momentJsonRecord103 :: acc := by rfl

noncomputable def momentTypedRecord103 : MomentRecord :=
  { simplexId := 103,
    factorFloorsQ80 := #[(1461038406409620613552 : Int), (1541138802069772928628 : Int), (289897922781386990977 : Int), (634826118040877779819 : Int), (1375044090364609591599 : Int), (2003805480916472201750 : Int), (1617957903093269244605 : Int), (1088892321465399704037 : Int), (1088867207826755829202 : Int), (1996180259431360131325 : Int)],
    oldFloorQ96 := (318025408099073 : Int),
    newFloorQ96 := (321489665851987 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_103_before_decode"
  err.flush

theorem decode_moment_record_103 :
    decodeMomentRecord momentJsonRecord103 = .ok momentTypedRecord103 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_103_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock025 : List SourceJson := [momentJsonRecord100, momentJsonRecord101, momentJsonRecord102, momentJsonRecord103]
noncomputable def momentTypedRecordsBlock025 : List MomentRecord := [momentTypedRecord100, momentTypedRecord101, momentTypedRecord102, momentTypedRecord103]

theorem moment_records_block_025_push_eq (acc : List SourceJson) :
    momentRecordsBlock025Push acc = [momentJsonRecord103, momentJsonRecord102, momentJsonRecord101, momentJsonRecord100] ++ acc := by rfl

theorem moment_records_block_025_reverse (acc : List SourceJson) :
    (momentRecordsBlock025Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock025 := by
  rw [moment_records_block_025_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_025 :
    momentJsonRecordsBlock025.mapM decodeMomentRecord = .ok momentTypedRecordsBlock025 := by
  simp only [momentJsonRecordsBlock025, momentTypedRecordsBlock025, List.mapM_cons, List.mapM_nil,
    decode_moment_record_100, decode_moment_record_101, decode_moment_record_102, decode_moment_record_103]
  rfl

noncomputable def momentTypedRowsThroughBlock025 : List MomentRecord := momentTypedRowsThroughBlock024 ++ momentTypedRecordsBlock025

theorem decode_moment_records_through_block_025 :
    momentRecordsAcc104.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock025 := by
  change (momentRecordsBlock025Push momentRecordsAcc100).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_025_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_024, decode_moment_records_block_025]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_025_complete"
  err.flush

#print axioms moment_record_100_push_eq
#print axioms decode_moment_record_100
#print axioms moment_record_101_push_eq
#print axioms decode_moment_record_101
#print axioms moment_record_102_push_eq
#print axioms decode_moment_record_102
#print axioms moment_record_103_push_eq
#print axioms decode_moment_record_103
#print axioms moment_records_block_025_push_eq
#print axioms moment_records_block_025_reverse
#print axioms decode_moment_records_block_025
#print axioms decode_moment_records_through_block_025

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
