import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock003
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock004

/-! Original typed moment records 16 through 19; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord016 : SourceJson :=
  (momentRecordsChunk016Push []).head (List.cons_ne_nil _ _)

theorem moment_record_016_push_eq (acc : List SourceJson) :
    momentRecordsChunk016Push acc = momentJsonRecord016 :: acc := by rfl

noncomputable def momentTypedRecord016 : MomentRecord :=
  { simplexId := 16,
    factorFloorsQ80 := #[(1455954806821788619522 : Int), (1595637769858588345574 : Int), (245463073208586796168 : Int), (340826255513531522807 : Int), (575683265790255019667 : Int), (1704040825685935058562 : Int), (934749979575132186907 : Int), (694635461729373360395 : Int), (916175104687170543377 : Int), (1043992426728146356507 : Int)],
    oldFloorQ96 := (13544586674269498002 : Int),
    newFloorQ96 := (13651523095432447917 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_016_before_decode"
  err.flush

theorem decode_moment_record_016 :
    decodeMomentRecord momentJsonRecord016 = .ok momentTypedRecord016 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_016_decoded"
  err.flush

noncomputable def momentJsonRecord017 : SourceJson :=
  (momentRecordsChunk017Push []).head (List.cons_ne_nil _ _)

theorem moment_record_017_push_eq (acc : List SourceJson) :
    momentRecordsChunk017Push acc = momentJsonRecord017 :: acc := by rfl

noncomputable def momentTypedRecord017 : MomentRecord :=
  { simplexId := 17,
    factorFloorsQ80 := #[(1147482594403172541745 : Int), (1363991817938746669254 : Int), (208447735418297345638 : Int), (162469688195508830124 : Int), (487727624193497857558 : Int), (1108252928730936263126 : Int), (947407705643068658683 : Int), (692447630981284820365 : Int), (906512114543424647314 : Int), (939999252162855024885 : Int)],
    oldFloorQ96 := (5922945504284076301 : Int),
    newFloorQ96 := (5962096340645448408 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_017_before_decode"
  err.flush

theorem decode_moment_record_017 :
    decodeMomentRecord momentJsonRecord017 = .ok momentTypedRecord017 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_017_decoded"
  err.flush

noncomputable def momentJsonRecord018 : SourceJson :=
  (momentRecordsChunk018Push []).head (List.cons_ne_nil _ _)

theorem moment_record_018_push_eq (acc : List SourceJson) :
    momentRecordsChunk018Push acc = momentJsonRecord018 :: acc := by rfl

noncomputable def momentTypedRecord018 : MomentRecord :=
  { simplexId := 18,
    factorFloorsQ80 := #[(1460569716284084953542 : Int), (1598851039520671553156 : Int), (255380683270330541385 : Int), (362171265481148353617 : Int), (512544943357191242873 : Int), (1645890026215138164986 : Int), (727997485334816345506 : Int), (664301587498151097054 : Int), (973542830085402815539 : Int), (1041378199972713442619 : Int)],
    oldFloorQ96 := (9091920852332181310 : Int),
    newFloorQ96 := (9161697912343749233 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_018_before_decode"
  err.flush

theorem decode_moment_record_018 :
    decodeMomentRecord momentJsonRecord018 = .ok momentTypedRecord018 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_018_decoded"
  err.flush

noncomputable def momentJsonRecord019 : SourceJson :=
  (momentRecordsChunk019Push []).head (List.cons_ne_nil _ _)

theorem moment_record_019_push_eq (acc : List SourceJson) :
    momentRecordsChunk019Push acc = momentJsonRecord019 :: acc := by rfl

noncomputable def momentTypedRecord019 : MomentRecord :=
  { simplexId := 19,
    factorFloorsQ80 := #[(1458954607536269925626 : Int), (1596588659656302421101 : Int), (264200936777363860707 : Int), (373233995570400105527 : Int), (665190736135762758061 : Int), (1737251243595756479493 : Int), (772747048058391650274 : Int), (816775492493031499126 : Int), (1179543296386035102517 : Int), (1036575746110805222971 : Int)],
    oldFloorQ96 := (13374270415670583315 : Int),
    newFloorQ96 := (13484255007890123356 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_019_before_decode"
  err.flush

theorem decode_moment_record_019 :
    decodeMomentRecord momentJsonRecord019 = .ok momentTypedRecord019 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_019_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock004 : List SourceJson := [momentJsonRecord016, momentJsonRecord017, momentJsonRecord018, momentJsonRecord019]
noncomputable def momentTypedRecordsBlock004 : List MomentRecord := [momentTypedRecord016, momentTypedRecord017, momentTypedRecord018, momentTypedRecord019]

theorem moment_records_block_004_push_eq (acc : List SourceJson) :
    momentRecordsBlock004Push acc = [momentJsonRecord019, momentJsonRecord018, momentJsonRecord017, momentJsonRecord016] ++ acc := by rfl

theorem moment_records_block_004_reverse (acc : List SourceJson) :
    (momentRecordsBlock004Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock004 := by
  rw [moment_records_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_004 :
    momentJsonRecordsBlock004.mapM decodeMomentRecord = .ok momentTypedRecordsBlock004 := by
  simp only [momentJsonRecordsBlock004, momentTypedRecordsBlock004, List.mapM_cons, List.mapM_nil,
    decode_moment_record_016, decode_moment_record_017, decode_moment_record_018, decode_moment_record_019]
  rfl

noncomputable def momentTypedRowsThroughBlock004 : List MomentRecord := momentTypedRowsThroughBlock003 ++ momentTypedRecordsBlock004

theorem decode_moment_records_through_block_004 :
    momentRecordsAcc020.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock004 := by
  change (momentRecordsBlock004Push momentRecordsAcc016).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_004_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_003, decode_moment_records_block_004]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_004_complete"
  err.flush

#print axioms moment_record_016_push_eq
#print axioms decode_moment_record_016
#print axioms moment_record_017_push_eq
#print axioms decode_moment_record_017
#print axioms moment_record_018_push_eq
#print axioms decode_moment_record_018
#print axioms moment_record_019_push_eq
#print axioms decode_moment_record_019
#print axioms moment_records_block_004_push_eq
#print axioms moment_records_block_004_reverse
#print axioms decode_moment_records_block_004
#print axioms decode_moment_records_through_block_004

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
