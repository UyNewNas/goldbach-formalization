import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock029
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock030

/-! Original typed moment records 120 through 123; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord120 : SourceJson :=
  (momentRecordsChunk120Push []).head (List.cons_ne_nil _ _)

theorem moment_record_120_push_eq (acc : List SourceJson) :
    momentRecordsChunk120Push acc = momentJsonRecord120 :: acc := by rfl

noncomputable def momentTypedRecord120 : MomentRecord :=
  { simplexId := 120,
    factorFloorsQ80 := #[(1129460764648042555337 : Int), (1306989522692808307158 : Int), (277737557322977938788 : Int), (261646397475238067618 : Int), (661544419432551956155 : Int), (1812828471988376655781 : Int), (1136670054279844392836 : Int), (783099196021410037695 : Int), (690437284032224569513 : Int), (690447762481849712004 : Int)],
    oldFloorQ96 := (331343152187326 : Int),
    newFloorQ96 := (333750295371456 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_120_before_decode"
  err.flush

theorem decode_moment_record_120 :
    decodeMomentRecord momentJsonRecord120 = .ok momentTypedRecord120 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_120_decoded"
  err.flush

noncomputable def momentJsonRecord121 : SourceJson :=
  (momentRecordsChunk121Push []).head (List.cons_ne_nil _ _)

theorem moment_record_121_push_eq (acc : List SourceJson) :
    momentRecordsChunk121Push acc = momentJsonRecord121 :: acc := by rfl

noncomputable def momentTypedRecord121 : MomentRecord :=
  { simplexId := 121,
    factorFloorsQ80 := #[(1404271363051803665384 : Int), (1514980308105410724960 : Int), (337357954302066496830 : Int), (496983957677528720058 : Int), (614736050562488932282 : Int), (2490543191911306605598 : Int), (979554515033999560039 : Int), (851894855807915778788 : Int), (741318552209789057350 : Int), (741333440445132704890 : Int)],
    oldFloorQ96 := (485644035639426 : Int),
    newFloorQ96 := (489747917866901 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_121_before_decode"
  err.flush

theorem decode_moment_record_121 :
    decodeMomentRecord momentJsonRecord121 = .ok momentTypedRecord121 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_121_decoded"
  err.flush

noncomputable def momentJsonRecord122 : SourceJson :=
  (momentRecordsChunk122Push []).head (List.cons_ne_nil _ _)

theorem moment_record_122_push_eq (acc : List SourceJson) :
    momentRecordsChunk122Push acc = momentJsonRecord122 :: acc := by rfl

noncomputable def momentTypedRecord122 : MomentRecord :=
  { simplexId := 122,
    factorFloorsQ80 := #[(1408136733707940761975 : Int), (1509581567408685745384 : Int), (349769833709759751951 : Int), (525453586465770049814 : Int), (727542692529931604361 : Int), (2624961742969032420402 : Int), (1079588539235133229639 : Int), (1081765608044154393074 : Int), (698172473379575985113 : Int), (698188428311002457421 : Int)],
    oldFloorQ96 := (699292987764046 : Int),
    newFloorQ96 := (705511628885835 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_122_before_decode"
  err.flush

theorem decode_moment_record_122 :
    decodeMomentRecord momentJsonRecord122 = .ok momentTypedRecord122 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_122_decoded"
  err.flush

noncomputable def momentJsonRecord123 : SourceJson :=
  (momentRecordsChunk123Push []).head (List.cons_ne_nil _ _)

theorem moment_record_123_push_eq (acc : List SourceJson) :
    momentRecordsChunk123Push acc = momentJsonRecord123 :: acc := by rfl

noncomputable def momentTypedRecord123 : MomentRecord :=
  { simplexId := 123,
    factorFloorsQ80 := #[(1352456280438462163217 : Int), (1436219113130607552834 : Int), (361179942436105632892 : Int), (544338906223941364452 : Int), (730110851671189655343 : Int), (2737927102418611982948 : Int), (1958628022847505289874 : Int), (1187956613997005542901 : Int), (555373957692998012497 : Int), (555391892960130457520 : Int)],
    oldFloorQ96 := (787047263077271 : Int),
    newFloorQ96 := (794516980588001 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_123_before_decode"
  err.flush

theorem decode_moment_record_123 :
    decodeMomentRecord momentJsonRecord123 = .ok momentTypedRecord123 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_123_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock030 : List SourceJson := [momentJsonRecord120, momentJsonRecord121, momentJsonRecord122, momentJsonRecord123]
noncomputable def momentTypedRecordsBlock030 : List MomentRecord := [momentTypedRecord120, momentTypedRecord121, momentTypedRecord122, momentTypedRecord123]

theorem moment_records_block_030_push_eq (acc : List SourceJson) :
    momentRecordsBlock030Push acc = [momentJsonRecord123, momentJsonRecord122, momentJsonRecord121, momentJsonRecord120] ++ acc := by rfl

theorem moment_records_block_030_reverse (acc : List SourceJson) :
    (momentRecordsBlock030Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock030 := by
  rw [moment_records_block_030_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_030 :
    momentJsonRecordsBlock030.mapM decodeMomentRecord = .ok momentTypedRecordsBlock030 := by
  simp only [momentJsonRecordsBlock030, momentTypedRecordsBlock030, List.mapM_cons, List.mapM_nil,
    decode_moment_record_120, decode_moment_record_121, decode_moment_record_122, decode_moment_record_123]
  rfl

noncomputable def momentTypedRowsThroughBlock030 : List MomentRecord := momentTypedRowsThroughBlock029 ++ momentTypedRecordsBlock030

theorem decode_moment_records_through_block_030 :
    momentRecordsAcc124.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock030 := by
  change (momentRecordsBlock030Push momentRecordsAcc120).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_030_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_029, decode_moment_records_block_030]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_030_complete"
  err.flush

#print axioms moment_record_120_push_eq
#print axioms decode_moment_record_120
#print axioms moment_record_121_push_eq
#print axioms decode_moment_record_121
#print axioms moment_record_122_push_eq
#print axioms decode_moment_record_122
#print axioms moment_record_123_push_eq
#print axioms decode_moment_record_123
#print axioms moment_records_block_030_push_eq
#print axioms moment_records_block_030_reverse
#print axioms decode_moment_records_block_030
#print axioms decode_moment_records_through_block_030

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
