import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock021
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock022

/-! Original typed moment records 88 through 91; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord088 : SourceJson :=
  (momentRecordsChunk088Push []).head (List.cons_ne_nil _ _)

theorem moment_record_088_push_eq (acc : List SourceJson) :
    momentRecordsChunk088Push acc = momentJsonRecord088 :: acc := by rfl

noncomputable def momentTypedRecord088 : MomentRecord :=
  { simplexId := 88,
    factorFloorsQ80 := #[(1352955455292434450841 : Int), (1429034962370106721621 : Int), (291020671343615532663 : Int), (637120592566887370279 : Int), (1379911482610497270538 : Int), (1894950327492023027456 : Int), (1457318904124820437256 : Int), (1184094405468034861117 : Int), (1143379977468861272131 : Int), (1584236108531181780499 : Int)],
    oldFloorQ96 := (662528105265205420 : Int),
    newFloorQ96 := (669333196540056706 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_088_before_decode"
  err.flush

theorem decode_moment_record_088 :
    decodeMomentRecord momentJsonRecord088 = .ok momentTypedRecord088 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_088_decoded"
  err.flush

noncomputable def momentJsonRecord089 : SourceJson :=
  (momentRecordsChunk089Push []).head (List.cons_ne_nil _ _)

theorem moment_record_089_push_eq (acc : List SourceJson) :
    momentRecordsChunk089Push acc = momentJsonRecord089 :: acc := by rfl

noncomputable def momentTypedRecord089 : MomentRecord :=
  { simplexId := 89,
    factorFloorsQ80 := #[(1988542855456757290213 : Int), (2083031570083909499151 : Int), (309796505479731510481 : Int), (766973560483197136171 : Int), (1478154438252854573086 : Int), (2313765984176992170686 : Int), (1725255759417891817997 : Int), (1475288084429850010802 : Int), (1504062592810258339646 : Int), (1504158396051619106918 : Int)],
    oldFloorQ96 := (9241777207506 : Int),
    newFloorQ96 := (9358314395506 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_089_before_decode"
  err.flush

theorem decode_moment_record_089 :
    decodeMomentRecord momentJsonRecord089 = .ok momentTypedRecord089 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_089_decoded"
  err.flush

noncomputable def momentJsonRecord090 : SourceJson :=
  (momentRecordsChunk090Push []).head (List.cons_ne_nil _ _)

theorem moment_record_090_push_eq (acc : List SourceJson) :
    momentRecordsChunk090Push acc = momentJsonRecord090 :: acc := by rfl

noncomputable def momentTypedRecord090 : MomentRecord :=
  { simplexId := 90,
    factorFloorsQ80 := #[(1730452310503628459884 : Int), (1889808620197738810347 : Int), (293697008922480591756 : Int), (691707649897996370371 : Int), (1492004345651810263333 : Int), (1894912382460056410525 : Int), (1665322139827150585163 : Int), (1414818379712645388347 : Int), (1379793130051249398665 : Int), (1584763345435350189844 : Int)],
    oldFloorQ96 := (94339675167185668 : Int),
    newFloorQ96 := (95441471829430727 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_090_before_decode"
  err.flush

theorem decode_moment_record_090 :
    decodeMomentRecord momentJsonRecord090 = .ok momentTypedRecord090 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_090_decoded"
  err.flush

noncomputable def momentJsonRecord091 : SourceJson :=
  (momentRecordsChunk091Push []).head (List.cons_ne_nil _ _)

theorem moment_record_091_push_eq (acc : List SourceJson) :
    momentRecordsChunk091Push acc = momentJsonRecord091 :: acc := by rfl

noncomputable def momentTypedRecord091 : MomentRecord :=
  { simplexId := 91,
    factorFloorsQ80 := #[(2273438058825159398833 : Int), (2221276606942419847510 : Int), (258160839018391674007 : Int), (816550413655689988484 : Int), (1234207853357288293616 : Int), (2317912327861891724880 : Int), (1605333932020590959164 : Int), (1436122196802673713934 : Int), (1272835416865340873574 : Int), (1272953256306192568485 : Int)],
    oldFloorQ96 := (251782756323 : Int),
    newFloorQ96 := (254864864969 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_091_before_decode"
  err.flush

theorem decode_moment_record_091 :
    decodeMomentRecord momentJsonRecord091 = .ok momentTypedRecord091 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_091_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock022 : List SourceJson := [momentJsonRecord088, momentJsonRecord089, momentJsonRecord090, momentJsonRecord091]
noncomputable def momentTypedRecordsBlock022 : List MomentRecord := [momentTypedRecord088, momentTypedRecord089, momentTypedRecord090, momentTypedRecord091]

theorem moment_records_block_022_push_eq (acc : List SourceJson) :
    momentRecordsBlock022Push acc = [momentJsonRecord091, momentJsonRecord090, momentJsonRecord089, momentJsonRecord088] ++ acc := by rfl

theorem moment_records_block_022_reverse (acc : List SourceJson) :
    (momentRecordsBlock022Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock022 := by
  rw [moment_records_block_022_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_022 :
    momentJsonRecordsBlock022.mapM decodeMomentRecord = .ok momentTypedRecordsBlock022 := by
  simp only [momentJsonRecordsBlock022, momentTypedRecordsBlock022, List.mapM_cons, List.mapM_nil,
    decode_moment_record_088, decode_moment_record_089, decode_moment_record_090, decode_moment_record_091]
  rfl

noncomputable def momentTypedRowsThroughBlock022 : List MomentRecord := momentTypedRowsThroughBlock021 ++ momentTypedRecordsBlock022

theorem decode_moment_records_through_block_022 :
    momentRecordsAcc092.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock022 := by
  change (momentRecordsBlock022Push momentRecordsAcc088).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_022_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_021, decode_moment_records_block_022]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_022_complete"
  err.flush

#print axioms moment_record_088_push_eq
#print axioms decode_moment_record_088
#print axioms moment_record_089_push_eq
#print axioms decode_moment_record_089
#print axioms moment_record_090_push_eq
#print axioms decode_moment_record_090
#print axioms moment_record_091_push_eq
#print axioms decode_moment_record_091
#print axioms moment_records_block_022_push_eq
#print axioms moment_records_block_022_reverse
#print axioms decode_moment_records_block_022
#print axioms decode_moment_records_through_block_022

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
