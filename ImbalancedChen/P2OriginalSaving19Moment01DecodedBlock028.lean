import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock027
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock028

/-! Original typed moment records 112 through 115; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord112 : SourceJson :=
  (momentRecordsChunk112Push []).head (List.cons_ne_nil _ _)

theorem moment_record_112_push_eq (acc : List SourceJson) :
    momentRecordsChunk112Push acc = momentJsonRecord112 :: acc := by rfl

noncomputable def momentTypedRecord112 : MomentRecord :=
  { simplexId := 112,
    factorFloorsQ80 := #[(1972005792062237962446 : Int), (1929454889059069820153 : Int), (157522661545770868718 : Int), (857692569330031575873 : Int), (1324860991802011371514 : Int), (1709538544961490609604 : Int), (1390194611254496568685 : Int), (1262254430601447941645 : Int), (1144223722391017916592 : Int), (1144315380477849307147 : Int)],
    oldFloorQ96 := (54957906838 : Int),
    newFloorQ96 := (55547117610 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_112_before_decode"
  err.flush

theorem decode_moment_record_112 :
    decodeMomentRecord momentJsonRecord112 = .ok momentTypedRecord112 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_112_decoded"
  err.flush

noncomputable def momentJsonRecord113 : SourceJson :=
  (momentRecordsChunk113Push []).head (List.cons_ne_nil _ _)

theorem moment_record_113_push_eq (acc : List SourceJson) :
    momentRecordsChunk113Push acc = momentJsonRecord113 :: acc := by rfl

noncomputable def momentTypedRecord113 : MomentRecord :=
  { simplexId := 113,
    factorFloorsQ80 := #[(1320790130122024885032 : Int), (1285751309880350408803 : Int), (144501692140980604573 : Int), (715986271898811571283 : Int), (806945206169064372690 : Int), (1424653992531979046490 : Int), (1090790264094788139934 : Int), (988921633069927323243 : Int), (950460806527979356945 : Int), (958660142942475922303 : Int)],
    oldFloorQ96 := (1334585446519187 : Int),
    newFloorQ96 := (1345322816875032 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_113_before_decode"
  err.flush

theorem decode_moment_record_113 :
    decodeMomentRecord momentJsonRecord113 = .ok momentTypedRecord113 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_113_decoded"
  err.flush

noncomputable def momentJsonRecord114 : SourceJson :=
  (momentRecordsChunk114Push []).head (List.cons_ne_nil _ _)

theorem moment_record_114_push_eq (acc : List SourceJson) :
    momentRecordsChunk114Push acc = momentJsonRecord114 :: acc := by rfl

noncomputable def momentTypedRecord114 : MomentRecord :=
  { simplexId := 114,
    factorFloorsQ80 := #[(1380285128862021314372 : Int), (1350209826057632544183 : Int), (138478354353771389714 : Int), (779224508561145939349 : Int), (791435588324857928932 : Int), (1403404661148212200233 : Int), (1116134852272958821695 : Int), (1024417337149912404777 : Int), (945878627330260726359 : Int), (945954830185193063100 : Int)],
    oldFloorQ96 := (52237229652 : Int),
    newFloorQ96 := (52665690599 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_114_before_decode"
  err.flush

theorem decode_moment_record_114 :
    decodeMomentRecord momentJsonRecord114 = .ok momentTypedRecord114 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_114_decoded"
  err.flush

noncomputable def momentJsonRecord115 : SourceJson :=
  (momentRecordsChunk115Push []).head (List.cons_ne_nil _ _)

theorem moment_record_115_push_eq (acc : List SourceJson) :
    momentRecordsChunk115Push acc = momentJsonRecord115 :: acc := by rfl

noncomputable def momentTypedRecord115 : MomentRecord :=
  { simplexId := 115,
    factorFloorsQ80 := #[(1406426919460017209614 : Int), (1359314792777383187241 : Int), (137783393093308355537 : Int), (750759523365274453394 : Int), (794914400905540899369 : Int), (1357191263109155513365 : Int), (1114938149206467203310 : Int), (1022717765089680184596 : Int), (948835836471551962646 : Int), (934107088309605097197 : Int)],
    oldFloorQ96 := (125294286594493 : Int),
    newFloorQ96 := (126316916290375 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_115_before_decode"
  err.flush

theorem decode_moment_record_115 :
    decodeMomentRecord momentJsonRecord115 = .ok momentTypedRecord115 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_115_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock028 : List SourceJson := [momentJsonRecord112, momentJsonRecord113, momentJsonRecord114, momentJsonRecord115]
noncomputable def momentTypedRecordsBlock028 : List MomentRecord := [momentTypedRecord112, momentTypedRecord113, momentTypedRecord114, momentTypedRecord115]

theorem moment_records_block_028_push_eq (acc : List SourceJson) :
    momentRecordsBlock028Push acc = [momentJsonRecord115, momentJsonRecord114, momentJsonRecord113, momentJsonRecord112] ++ acc := by rfl

theorem moment_records_block_028_reverse (acc : List SourceJson) :
    (momentRecordsBlock028Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock028 := by
  rw [moment_records_block_028_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_028 :
    momentJsonRecordsBlock028.mapM decodeMomentRecord = .ok momentTypedRecordsBlock028 := by
  simp only [momentJsonRecordsBlock028, momentTypedRecordsBlock028, List.mapM_cons, List.mapM_nil,
    decode_moment_record_112, decode_moment_record_113, decode_moment_record_114, decode_moment_record_115]
  rfl

noncomputable def momentTypedRowsThroughBlock028 : List MomentRecord := momentTypedRowsThroughBlock027 ++ momentTypedRecordsBlock028

theorem decode_moment_records_through_block_028 :
    momentRecordsAcc116.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock028 := by
  change (momentRecordsBlock028Push momentRecordsAcc112).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_028_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_027, decode_moment_records_block_028]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_028_complete"
  err.flush

#print axioms moment_record_112_push_eq
#print axioms decode_moment_record_112
#print axioms moment_record_113_push_eq
#print axioms decode_moment_record_113
#print axioms moment_record_114_push_eq
#print axioms decode_moment_record_114
#print axioms moment_record_115_push_eq
#print axioms decode_moment_record_115
#print axioms moment_records_block_028_push_eq
#print axioms moment_records_block_028_reverse
#print axioms decode_moment_records_block_028
#print axioms decode_moment_records_through_block_028

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
