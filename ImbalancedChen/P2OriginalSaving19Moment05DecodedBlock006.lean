import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock005
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock006

/-! Original typed moment records 24 through 27; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord024 : SourceJson :=
  (momentRecordsChunk024Push []).head (List.cons_ne_nil _ _)

theorem moment_record_024_push_eq (acc : List SourceJson) :
    momentRecordsChunk024Push acc = momentJsonRecord024 :: acc := by rfl

noncomputable def momentTypedRecord024 : MomentRecord :=
  { simplexId := 24,
    factorFloorsQ80 := #[(270520859304953578979 : Int), (305285091847672798431 : Int), (167731553307833668278 : Int), (338528290473583744112 : Int), (393061928368324236590 : Int), (339499146765152017658 : Int), (1209816969163001397990 : Int), (304963319462694140675 : Int), (372749696866458433795 : Int), (182811229330916346473 : Int)],
    oldFloorQ96 := (5714675449694439 : Int),
    newFloorQ96 := (5733069500312784 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_024_before_decode"
  err.flush

theorem decode_moment_record_024 :
    decodeMomentRecord momentJsonRecord024 = .ok momentTypedRecord024 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_024_decoded"
  err.flush

noncomputable def momentJsonRecord025 : SourceJson :=
  (momentRecordsChunk025Push []).head (List.cons_ne_nil _ _)

theorem moment_record_025_push_eq (acc : List SourceJson) :
    momentRecordsChunk025Push acc = momentJsonRecord025 :: acc := by rfl

noncomputable def momentTypedRecord025 : MomentRecord :=
  { simplexId := 25,
    factorFloorsQ80 := #[(258520621343981239951 : Int), (311219065059964371538 : Int), (171036803383347067462 : Int), (327959291067440519001 : Int), (347628519874346069277 : Int), (413648746491309617918 : Int), (1707693705762381962426 : Int), (283289323010057227370 : Int), (228771738836172129365 : Int), (228763013709748073458 : Int)],
    oldFloorQ96 := (744086457210 : Int),
    newFloorQ96 := (746724532270 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_025_before_decode"
  err.flush

theorem decode_moment_record_025 :
    decodeMomentRecord momentJsonRecord025 = .ok momentTypedRecord025 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_025_decoded"
  err.flush

noncomputable def momentJsonRecord026 : SourceJson :=
  (momentRecordsChunk026Push []).head (List.cons_ne_nil _ _)

theorem moment_record_026_push_eq (acc : List SourceJson) :
    momentRecordsChunk026Push acc = momentJsonRecord026 :: acc := by rfl

noncomputable def momentTypedRecord026 : MomentRecord :=
  { simplexId := 26,
    factorFloorsQ80 := #[(255464979232645734538 : Int), (328861413463737996717 : Int), (157380992270779323282 : Int), (254342457307178240719 : Int), (352323966614261377224 : Int), (307211816023848825448 : Int), (1275325295703594489791 : Int), (306558903039694782128 : Int), (317555010016313482108 : Int), (239649145416823721599 : Int)],
    oldFloorQ96 := (3949539773418603 : Int),
    newFloorQ96 := (3961956384691214 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_026_before_decode"
  err.flush

theorem decode_moment_record_026 :
    decodeMomentRecord momentJsonRecord026 = .ok momentTypedRecord026 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_026_decoded"
  err.flush

noncomputable def momentJsonRecord027 : SourceJson :=
  (momentRecordsChunk027Push []).head (List.cons_ne_nil _ _)

theorem moment_record_027_push_eq (acc : List SourceJson) :
    momentRecordsChunk027Push acc = momentJsonRecord027 :: acc := by rfl

noncomputable def momentTypedRecord027 : MomentRecord :=
  { simplexId := 27,
    factorFloorsQ80 := #[(229751078644815388792 : Int), (288933241259562453216 : Int), (135520950290108104971 : Int), (226222747934203170808 : Int), (305391428160535856688 : Int), (289271984851991720880 : Int), (1320968529936508951289 : Int), (355525433829996011555 : Int), (369290623326179522660 : Int), (245890880444590295824 : Int)],
    oldFloorQ96 := (890947442453 : Int),
    newFloorQ96 := (893727782656 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_027_before_decode"
  err.flush

theorem decode_moment_record_027 :
    decodeMomentRecord momentJsonRecord027 = .ok momentTypedRecord027 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_027_decoded"
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
  err.putStrLn "P26_MOMENT05 typed_block_006_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
