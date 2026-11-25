import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock004
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock005

/-! Original typed moment records 20 through 23; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord020 : SourceJson :=
  (momentRecordsChunk020Push []).head (List.cons_ne_nil _ _)

theorem moment_record_020_push_eq (acc : List SourceJson) :
    momentRecordsChunk020Push acc = momentJsonRecord020 :: acc := by rfl

noncomputable def momentTypedRecord020 : MomentRecord :=
  { simplexId := 20,
    factorFloorsQ80 := #[(314920077601715716835 : Int), (381511416197297753012 : Int), (155200649328413768474 : Int), (271180456853100127323 : Int), (317004670205797228710 : Int), (321319554452275239648 : Int), (319968301851455248397 : Int), (334243445823868464728 : Int), (437836061963703846358 : Int), (262484214395399403974 : Int)],
    oldFloorQ96 := (3315994689295 : Int),
    newFloorQ96 := (3324551761993 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_020_before_decode"
  err.flush

theorem decode_moment_record_020 :
    decodeMomentRecord momentJsonRecord020 = .ok momentTypedRecord020 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_020_decoded"
  err.flush

noncomputable def momentJsonRecord021 : SourceJson :=
  (momentRecordsChunk021Push []).head (List.cons_ne_nil _ _)

theorem moment_record_021_push_eq (acc : List SourceJson) :
    momentRecordsChunk021Push acc = momentJsonRecord021 :: acc := by rfl

noncomputable def momentTypedRecord021 : MomentRecord :=
  { simplexId := 21,
    factorFloorsQ80 := #[(156445035760094367332 : Int), (238799688611244183336 : Int), (105737150938745334603 : Int), (92396357745710968337 : Int), (212727931839268649366 : Int), (123007470375280313961 : Int), (301315615600731246973 : Int), (290516602963852787318 : Int), (365468264147412375565 : Int), (163516098191158770213 : Int)],
    oldFloorQ96 := (2490576078707 : Int),
    newFloorQ96 := (2494802837811 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_021_before_decode"
  err.flush

theorem decode_moment_record_021 :
    decodeMomentRecord momentJsonRecord021 = .ok momentTypedRecord021 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_021_decoded"
  err.flush

noncomputable def momentJsonRecord022 : SourceJson :=
  (momentRecordsChunk022Push []).head (List.cons_ne_nil _ _)

theorem moment_record_022_push_eq (acc : List SourceJson) :
    momentRecordsChunk022Push acc = momentJsonRecord022 :: acc := by rfl

noncomputable def momentTypedRecord022 : MomentRecord :=
  { simplexId := 22,
    factorFloorsQ80 := #[(215273358779618225506 : Int), (329575781323670016172 : Int), (139235021588497547401 : Int), (133419657501586542454 : Int), (273425879667632150244 : Int), (154412977407570804031 : Int), (275985474531098958826 : Int), (321948023328444225612 : Int), (355714898032948422110 : Int), (215369333813061021898 : Int)],
    oldFloorQ96 := (13767178061220172 : Int),
    newFloorQ96 := (13794700132552503 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_022_before_decode"
  err.flush

theorem decode_moment_record_022 :
    decodeMomentRecord momentJsonRecord022 = .ok momentTypedRecord022 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_022_decoded"
  err.flush

noncomputable def momentJsonRecord023 : SourceJson :=
  (momentRecordsChunk023Push []).head (List.cons_ne_nil _ _)

theorem moment_record_023_push_eq (acc : List SourceJson) :
    momentRecordsChunk023Push acc = momentJsonRecord023 :: acc := by rfl

noncomputable def momentTypedRecord023 : MomentRecord :=
  { simplexId := 23,
    factorFloorsQ80 := #[(151541683360734019744 : Int), (238103080491085529660 : Int), (104801997148768433116 : Int), (86722221032893350501 : Int), (182667879590186987095 : Int), (114829533388516002240 : Int), (237485057791737871285 : Int), (250103053143354961382 : Int), (345323531862409171762 : Int), (155437243688159443359 : Int)],
    oldFloorQ96 := (11126336058764328 : Int),
    newFloorQ96 := (11143532389492423 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_023_before_decode"
  err.flush

theorem decode_moment_record_023 :
    decodeMomentRecord momentJsonRecord023 = .ok momentTypedRecord023 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_023_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock005 : List SourceJson := [momentJsonRecord020, momentJsonRecord021, momentJsonRecord022, momentJsonRecord023]
noncomputable def momentTypedRecordsBlock005 : List MomentRecord := [momentTypedRecord020, momentTypedRecord021, momentTypedRecord022, momentTypedRecord023]

theorem moment_records_block_005_push_eq (acc : List SourceJson) :
    momentRecordsBlock005Push acc = [momentJsonRecord023, momentJsonRecord022, momentJsonRecord021, momentJsonRecord020] ++ acc := by rfl

theorem moment_records_block_005_reverse (acc : List SourceJson) :
    (momentRecordsBlock005Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock005 := by
  rw [moment_records_block_005_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_005 :
    momentJsonRecordsBlock005.mapM decodeMomentRecord = .ok momentTypedRecordsBlock005 := by
  simp only [momentJsonRecordsBlock005, momentTypedRecordsBlock005, List.mapM_cons, List.mapM_nil,
    decode_moment_record_020, decode_moment_record_021, decode_moment_record_022, decode_moment_record_023]
  rfl

noncomputable def momentTypedRowsThroughBlock005 : List MomentRecord := momentTypedRowsThroughBlock004 ++ momentTypedRecordsBlock005

theorem decode_moment_records_through_block_005 :
    momentRecordsAcc024.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock005 := by
  change (momentRecordsBlock005Push momentRecordsAcc020).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_005_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_004, decode_moment_records_block_005]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_block_005_complete"
  err.flush

#print axioms moment_record_020_push_eq
#print axioms decode_moment_record_020
#print axioms moment_record_021_push_eq
#print axioms decode_moment_record_021
#print axioms moment_record_022_push_eq
#print axioms decode_moment_record_022
#print axioms moment_record_023_push_eq
#print axioms decode_moment_record_023
#print axioms moment_records_block_005_push_eq
#print axioms moment_records_block_005_reverse
#print axioms decode_moment_records_block_005
#print axioms decode_moment_records_through_block_005

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
