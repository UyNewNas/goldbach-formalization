import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock007
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock008

/-! Original typed moment records 32 through 35; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord032 : SourceJson :=
  (momentRecordsChunk032Push []).head (List.cons_ne_nil _ _)

theorem moment_record_032_push_eq (acc : List SourceJson) :
    momentRecordsChunk032Push acc = momentJsonRecord032 :: acc := by rfl

noncomputable def momentTypedRecord032 : MomentRecord :=
  { simplexId := 32,
    factorFloorsQ80 := #[(1618593740168426646372 : Int), (1697479366312195535274 : Int), (263548907531635481967 : Int), (434323622865591906893 : Int), (760884512692258124756 : Int), (1744327469024535603583 : Int), (1706781574112561321641 : Int), (893151352984524979620 : Int), (957416066534825341515 : Int), (1028618248502203150413 : Int)],
    oldFloorQ96 := (15734722406358686793 : Int),
    newFloorQ96 := (15879926577992852241 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_032_before_decode"
  err.flush

theorem decode_moment_record_032 :
    decodeMomentRecord momentJsonRecord032 = .ok momentTypedRecord032 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_032_decoded"
  err.flush

noncomputable def momentJsonRecord033 : SourceJson :=
  (momentRecordsChunk033Push []).head (List.cons_ne_nil _ _)

theorem moment_record_033_push_eq (acc : List SourceJson) :
    momentRecordsChunk033Push acc = momentJsonRecord033 :: acc := by rfl

noncomputable def momentTypedRecord033 : MomentRecord :=
  { simplexId := 33,
    factorFloorsQ80 := #[(1594524321012899840144 : Int), (1697240168803635249117 : Int), (263549029040133356647 : Int), (424202740551278798262 : Int), (787821304039692366114 : Int), (1803911532826232977584 : Int), (1705359268230153172004 : Int), (921280102042220550355 : Int), (1000393371559994953064 : Int), (1217425818887233715303 : Int)],
    oldFloorQ96 := (25488273854866261798 : Int),
    newFloorQ96 := (25730095793037855874 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_033_before_decode"
  err.flush

theorem decode_moment_record_033 :
    decodeMomentRecord momentJsonRecord033 = .ok momentTypedRecord033 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_033_decoded"
  err.flush

noncomputable def momentJsonRecord034 : SourceJson :=
  (momentRecordsChunk034Push []).head (List.cons_ne_nil _ _)

theorem moment_record_034_push_eq (acc : List SourceJson) :
    momentRecordsChunk034Push acc = momentJsonRecord034 :: acc := by rfl

noncomputable def momentTypedRecord034 : MomentRecord :=
  { simplexId := 34,
    factorFloorsQ80 := #[(1594521378863697150487 : Int), (1697238062683406730629 : Int), (263549106739042794543 : Int), (424202518119466986005 : Int), (787820421921059971270 : Int), (1803912355830065731330 : Int), (2220101257965339749757 : Int), (1000372384716346299838 : Int), (1000365012836481682231 : Int), (1217430459292959195787 : Int)],
    oldFloorQ96 := (1389050284689611 : Int),
    newFloorQ96 := (1402917926844895 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_034_before_decode"
  err.flush

theorem decode_moment_record_034 :
    decodeMomentRecord momentJsonRecord034 = .ok momentTypedRecord034 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_034_decoded"
  err.flush

noncomputable def momentJsonRecord035 : SourceJson :=
  (momentRecordsChunk035Push []).head (List.cons_ne_nil _ _)

theorem moment_record_035_push_eq (acc : List SourceJson) :
    momentRecordsChunk035Push acc = momentJsonRecord035 :: acc := by rfl

noncomputable def momentTypedRecord035 : MomentRecord :=
  { simplexId := 35,
    factorFloorsQ80 := #[(2144803235885918761158 : Int), (2250233504170218834653 : Int), (285738166894873981094 : Int), (565452933438916867879 : Int), (880184646308761595479 : Int), (2033000269898367110636 : Int), (1277262103814624336436 : Int), (979147240138777753471 : Int), (1195098328282324675592 : Int), (1195130359104036742689 : Int)],
    oldFloorQ96 := (202937476174847 : Int),
    newFloorQ96 := (205098602001783 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_035_before_decode"
  err.flush

theorem decode_moment_record_035 :
    decodeMomentRecord momentJsonRecord035 = .ok momentTypedRecord035 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_035_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock008 : List SourceJson := [momentJsonRecord032, momentJsonRecord033, momentJsonRecord034, momentJsonRecord035]
noncomputable def momentTypedRecordsBlock008 : List MomentRecord := [momentTypedRecord032, momentTypedRecord033, momentTypedRecord034, momentTypedRecord035]

theorem moment_records_block_008_push_eq (acc : List SourceJson) :
    momentRecordsBlock008Push acc = [momentJsonRecord035, momentJsonRecord034, momentJsonRecord033, momentJsonRecord032] ++ acc := by rfl

theorem moment_records_block_008_reverse (acc : List SourceJson) :
    (momentRecordsBlock008Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock008 := by
  rw [moment_records_block_008_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_008 :
    momentJsonRecordsBlock008.mapM decodeMomentRecord = .ok momentTypedRecordsBlock008 := by
  simp only [momentJsonRecordsBlock008, momentTypedRecordsBlock008, List.mapM_cons, List.mapM_nil,
    decode_moment_record_032, decode_moment_record_033, decode_moment_record_034, decode_moment_record_035]
  rfl

noncomputable def momentTypedRowsThroughBlock008 : List MomentRecord := momentTypedRowsThroughBlock007 ++ momentTypedRecordsBlock008

theorem decode_moment_records_through_block_008 :
    momentRecordsAcc036.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock008 := by
  change (momentRecordsBlock008Push momentRecordsAcc032).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_008_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_007, decode_moment_records_block_008]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_008_complete"
  err.flush

#print axioms moment_record_032_push_eq
#print axioms decode_moment_record_032
#print axioms moment_record_033_push_eq
#print axioms decode_moment_record_033
#print axioms moment_record_034_push_eq
#print axioms decode_moment_record_034
#print axioms moment_record_035_push_eq
#print axioms decode_moment_record_035
#print axioms moment_records_block_008_push_eq
#print axioms moment_records_block_008_reverse
#print axioms decode_moment_records_block_008
#print axioms decode_moment_records_through_block_008

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
