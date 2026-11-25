import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock005
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock006

/-! Original typed moment records 24 through 27; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord024 : SourceJson :=
  (momentRecordsChunk024Push []).head (List.cons_ne_nil _ _)

theorem moment_record_024_push_eq (acc : List SourceJson) :
    momentRecordsChunk024Push acc = momentJsonRecord024 :: acc := by rfl

noncomputable def momentTypedRecord024 : MomentRecord :=
  { simplexId := 24,
    factorFloorsQ80 := #[(1327822507584570281969 : Int), (1413495690831275807779 : Int), (268103927807509208545 : Int), (372954781831739395930 : Int), (768424184510378328227 : Int), (1830513019106409177963 : Int), (2116067432953050606340 : Int), (1031136795544112243016 : Int), (1031218194338510382228 : Int), (649397292836484209710 : Int)],
    oldFloorQ96 := (1016236701288741 : Int),
    newFloorQ96 := (1025363723056279 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_024_before_decode"
  err.flush

theorem decode_moment_record_024 :
    decodeMomentRecord momentJsonRecord024 = .ok momentTypedRecord024 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_024_decoded"
  err.flush

noncomputable def momentJsonRecord025 : SourceJson :=
  (momentRecordsChunk025Push []).head (List.cons_ne_nil _ _)

theorem moment_record_025_push_eq (acc : List SourceJson) :
    momentRecordsChunk025Push acc = momentJsonRecord025 :: acc := by rfl

noncomputable def momentTypedRecord025 : MomentRecord :=
  { simplexId := 25,
    factorFloorsQ80 := #[(1455957721566617112383 : Int), (1595641360303443568946 : Int), (245462980263549559210 : Int), (340826373121813463736 : Int), (575682993413742670918 : Int), (1704040371864839015280 : Int), (1340454295760721546172 : Int), (916088911105572054210 : Int), (916136466034598715860 : Int), (1043998618458092749728 : Int)],
    oldFloorQ96 := (872667810396173 : Int),
    newFloorQ96 := (880014035253614 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_025_before_decode"
  err.flush

theorem decode_moment_record_025 :
    decodeMomentRecord momentJsonRecord025 = .ok momentTypedRecord025 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_025_decoded"
  err.flush

noncomputable def momentJsonRecord026 : SourceJson :=
  (momentRecordsChunk026Push []).head (List.cons_ne_nil _ _)

theorem moment_record_026_push_eq (acc : List SourceJson) :
    momentRecordsChunk026Push acc = momentJsonRecord026 :: acc := by rfl

noncomputable def momentTypedRecord026 : MomentRecord :=
  { simplexId := 26,
    factorFloorsQ80 := #[(1147484309915867900471 : Int), (1363994589097579064613 : Int), (208447667603982737426 : Int), (162469746751300668300 : Int), (487727421683917269612 : Int), (1108253337537708479198 : Int), (1360511768162584030508 : Int), (906426608756929251093 : Int), (906473784213689642842 : Int), (940004873313482673276 : Int)],
    oldFloorQ96 := (381615526940720 : Int),
    newFloorQ96 := (384337315662273 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_026_before_decode"
  err.flush

theorem decode_moment_record_026 :
    decodeMomentRecord momentJsonRecord026 = .ok momentTypedRecord026 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_026_decoded"
  err.flush

noncomputable def momentJsonRecord027 : SourceJson :=
  (momentRecordsChunk027Push []).head (List.cons_ne_nil _ _)

theorem moment_record_027_push_eq (acc : List SourceJson) :
    momentRecordsChunk027Push acc = momentJsonRecord027 :: acc := by rfl

noncomputable def momentTypedRecord027 : MomentRecord :=
  { simplexId := 27,
    factorFloorsQ80 := #[(1460572671737575624056 : Int), (1598854667840415363903 : Int), (255380575512184896645 : Int), (362171395062780846455 : Int), (512544414980455248753 : Int), (1645889747030899996508 : Int), (1044793208961838028575 : Int), (973448765896561909019 : Int), (973500663220174563601 : Int), (1041384416593271541002 : Int)],
    oldFloorQ96 := (585701008011563 : Int),
    newFloorQ96 := (590501691022202 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_027_before_decode"
  err.flush

theorem decode_moment_record_027 :
    decodeMomentRecord momentJsonRecord027 = .ok momentTypedRecord027 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_027_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock006 : List SourceJson := [momentJsonRecord024, momentJsonRecord025, momentJsonRecord026, momentJsonRecord027]
noncomputable def momentTypedRecordsBlock006 : List MomentRecord := [momentTypedRecord024, momentTypedRecord025, momentTypedRecord026, momentTypedRecord027]

theorem moment_records_block_006_push_eq (acc : List SourceJson) :
    momentRecordsBlock006Push acc = [momentJsonRecord027, momentJsonRecord026, momentJsonRecord025, momentJsonRecord024] ++ acc := by rfl

theorem moment_records_block_006_reverse (acc : List SourceJson) :
    (momentRecordsBlock006Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock006 := by
  rw [moment_records_block_006_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_006 :
    momentJsonRecordsBlock006.mapM decodeMomentRecord = .ok momentTypedRecordsBlock006 := by
  simp only [momentJsonRecordsBlock006, momentTypedRecordsBlock006, List.mapM_cons, List.mapM_nil,
    decode_moment_record_024, decode_moment_record_025, decode_moment_record_026, decode_moment_record_027]
  rfl

noncomputable def momentTypedRowsThroughBlock006 : List MomentRecord := momentTypedRowsThroughBlock005 ++ momentTypedRecordsBlock006

theorem decode_moment_records_through_block_006 :
    momentRecordsAcc028.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock006 := by
  change (momentRecordsBlock006Push momentRecordsAcc024).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_006_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_005, decode_moment_records_block_006]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_006_complete"
  err.flush

#print axioms moment_record_024_push_eq
#print axioms decode_moment_record_024
#print axioms moment_record_025_push_eq
#print axioms decode_moment_record_025
#print axioms moment_record_026_push_eq
#print axioms decode_moment_record_026
#print axioms moment_record_027_push_eq
#print axioms decode_moment_record_027
#print axioms moment_records_block_006_push_eq
#print axioms moment_records_block_006_reverse
#print axioms decode_moment_records_block_006
#print axioms decode_moment_records_through_block_006

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
