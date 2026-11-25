import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock023
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock024

/-! Original typed moment records 96 through 99; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord096 : SourceJson :=
  (momentRecordsChunk096Push []).head (List.cons_ne_nil _ _)

theorem moment_record_096_push_eq (acc : List SourceJson) :
    momentRecordsChunk096Push acc = momentJsonRecord096 :: acc := by rfl

noncomputable def momentTypedRecord096 : MomentRecord :=
  { simplexId := 96,
    factorFloorsQ80 := #[(1915952285941601505851 : Int), (1861613613231226057247 : Int), (220783552591971349706 : Int), (734946968908179864760 : Int), (1107547408822470302615 : Int), (1889719056870866210150 : Int), (1400210481936844084625 : Int), (1244552145713796952574 : Int), (1131100980557633155715 : Int), (1467656154331017107063 : Int)],
    oldFloorQ96 := (4646710149648680 : Int),
    newFloorQ96 := (4696846770143374 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_096_before_decode"
  err.flush

theorem decode_moment_record_096 :
    decodeMomentRecord momentJsonRecord096 = .ok momentTypedRecord096 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_096_decoded"
  err.flush

noncomputable def momentJsonRecord097 : SourceJson :=
  (momentRecordsChunk097Push []).head (List.cons_ne_nil _ _)

theorem moment_record_097_push_eq (acc : List SourceJson) :
    momentRecordsChunk097Push acc = momentJsonRecord097 :: acc := by rfl

noncomputable def momentTypedRecord097 : MomentRecord :=
  { simplexId := 97,
    factorFloorsQ80 := #[(1954813835405620371862 : Int), (1906399980728633148243 : Int), (204512922861125579780 : Int), (785001943091308012483 : Int), (1024619560368650164472 : Int), (1908917752714506013462 : Int), (1378973063018616474178 : Int), (1248017724822077351839 : Int), (1155443974400718088335 : Int), (1081207178952005874108 : Int)],
    oldFloorQ96 := (1553505016998030 : Int),
    newFloorQ96 := (1569843264841485 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_097_before_decode"
  err.flush

theorem decode_moment_record_097 :
    decodeMomentRecord momentJsonRecord097 = .ok momentTypedRecord097 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_097_decoded"
  err.flush

noncomputable def momentJsonRecord098 : SourceJson :=
  (momentRecordsChunk098Push []).head (List.cons_ne_nil _ _)

theorem moment_record_098_push_eq (acc : List SourceJson) :
    momentRecordsChunk098Push acc = momentJsonRecord098 :: acc := by rfl

noncomputable def momentTypedRecord098 : MomentRecord :=
  { simplexId := 98,
    factorFloorsQ80 := #[(1461050239941111303436 : Int), (1541151093540821274709 : Int), (289897950718654034110 : Int), (634830500072735369798 : Int), (1375048725668314197974 : Int), (2003804884203279387877 : Int), (1473451934465114712082 : Int), (1209465100769151281317 : Int), (1088865886120267709626 : Int), (1996222138002594884952 : Int)],
    oldFloorQ96 := (1273555064993981399 : Int),
    newFloorQ96 := (1287402519112997070 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_098_before_decode"
  err.flush

theorem decode_moment_record_098 :
    decodeMomentRecord momentJsonRecord098 = .ok momentTypedRecord098 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_098_decoded"
  err.flush

noncomputable def momentJsonRecord099 : SourceJson :=
  (momentRecordsChunk099Push []).head (List.cons_ne_nil _ _)

theorem moment_record_099_push_eq (acc : List SourceJson) :
    momentRecordsChunk099Push acc = momentJsonRecord099 :: acc := by rfl

noncomputable def momentTypedRecord099 : MomentRecord :=
  { simplexId := 99,
    factorFloorsQ80 := #[(1731056901078467753491 : Int), (1673551830241011884237 : Int), (234187289866436111172 : Int), (697599439560363099016 : Int), (1105168762557869154880 : Int), (2004462317349447816339 : Int), (1341551266534641374535 : Int), (1161715897817305107117 : Int), (1083880159807995977417 : Int), (1941166807680887134139 : Int)],
    oldFloorQ96 := (39048640284953688 : Int),
    newFloorQ96 := (39469971923976491 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_099_before_decode"
  err.flush

theorem decode_moment_record_099 :
    decodeMomentRecord momentJsonRecord099 = .ok momentTypedRecord099 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_099_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock024 : List SourceJson := [momentJsonRecord096, momentJsonRecord097, momentJsonRecord098, momentJsonRecord099]
noncomputable def momentTypedRecordsBlock024 : List MomentRecord := [momentTypedRecord096, momentTypedRecord097, momentTypedRecord098, momentTypedRecord099]

theorem moment_records_block_024_push_eq (acc : List SourceJson) :
    momentRecordsBlock024Push acc = [momentJsonRecord099, momentJsonRecord098, momentJsonRecord097, momentJsonRecord096] ++ acc := by rfl

theorem moment_records_block_024_reverse (acc : List SourceJson) :
    (momentRecordsBlock024Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock024 := by
  rw [moment_records_block_024_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_024 :
    momentJsonRecordsBlock024.mapM decodeMomentRecord = .ok momentTypedRecordsBlock024 := by
  simp only [momentJsonRecordsBlock024, momentTypedRecordsBlock024, List.mapM_cons, List.mapM_nil,
    decode_moment_record_096, decode_moment_record_097, decode_moment_record_098, decode_moment_record_099]
  rfl

noncomputable def momentTypedRowsThroughBlock024 : List MomentRecord := momentTypedRowsThroughBlock023 ++ momentTypedRecordsBlock024

theorem decode_moment_records_through_block_024 :
    momentRecordsAcc100.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock024 := by
  change (momentRecordsBlock024Push momentRecordsAcc096).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_024_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_023, decode_moment_records_block_024]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_024_complete"
  err.flush

#print axioms moment_record_096_push_eq
#print axioms decode_moment_record_096
#print axioms moment_record_097_push_eq
#print axioms decode_moment_record_097
#print axioms moment_record_098_push_eq
#print axioms decode_moment_record_098
#print axioms moment_record_099_push_eq
#print axioms decode_moment_record_099
#print axioms moment_records_block_024_push_eq
#print axioms moment_records_block_024_reverse
#print axioms decode_moment_records_block_024
#print axioms decode_moment_records_through_block_024

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
