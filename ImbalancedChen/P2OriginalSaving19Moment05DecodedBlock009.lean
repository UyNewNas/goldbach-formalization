import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock008
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock009

/-! Original typed moment records 36 through 39; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord036 : SourceJson :=
  (momentRecordsChunk036Push []).head (List.cons_ne_nil _ _)

theorem moment_record_036_push_eq (acc : List SourceJson) :
    momentRecordsChunk036Push acc = momentJsonRecord036 :: acc := by rfl

noncomputable def momentTypedRecord036 : MomentRecord :=
  { simplexId := 36,
    factorFloorsQ80 := #[(216083152718604084010 : Int), (271272714925490883095 : Int), (137835584624812475878 : Int), (226419606726726918104 : Int), (304017879042281530791 : Int), (294266782381972821114 : Int), (1563736124946978066905 : Int), (284032029666006459611 : Int), (302629262409879778898 : Int), (215370222772307509639 : Int)],
    oldFloorQ96 := (1031972851932 : Int),
    newFloorQ96 := (1035235154366 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_036_before_decode"
  err.flush

theorem decode_moment_record_036 :
    decodeMomentRecord momentJsonRecord036 = .ok momentTypedRecord036 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_036_decoded"
  err.flush

noncomputable def momentJsonRecord037 : SourceJson :=
  (momentRecordsChunk037Push []).head (List.cons_ne_nil _ _)

theorem moment_record_037_push_eq (acc : List SourceJson) :
    momentRecordsChunk037Push acc = momentJsonRecord037 :: acc := by rfl

noncomputable def momentTypedRecord037 : MomentRecord :=
  { simplexId := 37,
    factorFloorsQ80 := #[(177551866594934875416 : Int), (229835251379845759707 : Int), (82931470048141827636 : Int), (105459677723570370264 : Int), (205947712715075805156 : Int), (124111649260211145727 : Int), (818726620718411120990 : Int), (279000608575962934247 : Int), (285716566324709258764 : Int), (202586758676530315972 : Int)],
    oldFloorQ96 := (1145669186501 : Int),
    newFloorQ96 := (1148052096743 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_037_before_decode"
  err.flush

theorem decode_moment_record_037 :
    decodeMomentRecord momentJsonRecord037 = .ok momentTypedRecord037 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_037_decoded"
  err.flush

noncomputable def momentJsonRecord038 : SourceJson :=
  (momentRecordsChunk038Push []).head (List.cons_ne_nil _ _)

theorem moment_record_038_push_eq (acc : List SourceJson) :
    momentRecordsChunk038Push acc = momentJsonRecord038 :: acc := by rfl

noncomputable def momentTypedRecord038 : MomentRecord :=
  { simplexId := 38,
    factorFloorsQ80 := #[(415677853760938752098 : Int), (449736796555584198870 : Int), (174575564192358152130 : Int), (409849237419132128542 : Int), (379112232913398535568 : Int), (380270087106412970486 : Int), (978716170581541046848 : Int), (340416525130398640074 : Int), (497331733653331537332 : Int), (323966152285457565505 : Int)],
    oldFloorQ96 := (17757997147096458 : Int),
    newFloorQ96 := (17822004577693952 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_038_before_decode"
  err.flush

theorem decode_moment_record_038 :
    decodeMomentRecord momentJsonRecord038 = .ok momentTypedRecord038 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_038_decoded"
  err.flush

noncomputable def momentJsonRecord039 : SourceJson :=
  (momentRecordsChunk039Push []).head (List.cons_ne_nil _ _)

theorem moment_record_039_push_eq (acc : List SourceJson) :
    momentRecordsChunk039Push acc = momentJsonRecord039 :: acc := by rfl

noncomputable def momentTypedRecord039 : MomentRecord :=
  { simplexId := 39,
    factorFloorsQ80 := #[(416967169439294230015 : Int), (451867349854270391184 : Int), (178058574721811752806 : Int), (411842487566590645209 : Int), (378091959784575388039 : Int), (378224548485901210646 : Int), (1282170135783479046971 : Int), (253655064282582793540 : Int), (361524858113572219499 : Int), (328809115579577596597 : Int)],
    oldFloorQ96 := (16994873490384452 : Int),
    newFloorQ96 := (17057422104159878 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_039_before_decode"
  err.flush

theorem decode_moment_record_039 :
    decodeMomentRecord momentJsonRecord039 = .ok momentTypedRecord039 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_039_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock009 : List SourceJson := [momentJsonRecord036, momentJsonRecord037, momentJsonRecord038, momentJsonRecord039]
noncomputable def momentTypedRecordsBlock009 : List MomentRecord := [momentTypedRecord036, momentTypedRecord037, momentTypedRecord038, momentTypedRecord039]

theorem moment_records_block_009_push_eq (acc : List SourceJson) :
    momentRecordsBlock009Push acc = [momentJsonRecord039, momentJsonRecord038, momentJsonRecord037, momentJsonRecord036] ++ acc := by rfl

theorem moment_records_block_009_reverse (acc : List SourceJson) :
    (momentRecordsBlock009Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock009 := by
  rw [moment_records_block_009_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_009 :
    momentJsonRecordsBlock009.mapM decodeMomentRecord = .ok momentTypedRecordsBlock009 := by
  simp only [momentJsonRecordsBlock009, momentTypedRecordsBlock009, List.mapM_cons, List.mapM_nil,
    decode_moment_record_036, decode_moment_record_037, decode_moment_record_038, decode_moment_record_039]
  rfl

noncomputable def momentTypedRowsThroughBlock009 : List MomentRecord := momentTypedRowsThroughBlock008 ++ momentTypedRecordsBlock009

theorem decode_moment_records_through_block_009 :
    momentRecordsAcc040.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock009 := by
  change (momentRecordsBlock009Push momentRecordsAcc036).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_009_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_008, decode_moment_records_block_009]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_block_009_complete"
  err.flush

#print axioms moment_record_036_push_eq
#print axioms decode_moment_record_036
#print axioms moment_record_037_push_eq
#print axioms decode_moment_record_037
#print axioms moment_record_038_push_eq
#print axioms decode_moment_record_038
#print axioms moment_record_039_push_eq
#print axioms decode_moment_record_039
#print axioms moment_records_block_009_push_eq
#print axioms moment_records_block_009_reverse
#print axioms decode_moment_records_block_009
#print axioms decode_moment_records_through_block_009

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
