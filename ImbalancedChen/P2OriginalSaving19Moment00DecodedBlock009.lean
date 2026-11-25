import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock008
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock009

/-! Original typed moment records 36 through 39; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord036 : SourceJson :=
  (momentRecordsChunk036Push []).head (List.cons_ne_nil _ _)

theorem moment_record_036_push_eq (acc : List SourceJson) :
    momentRecordsChunk036Push acc = momentJsonRecord036 :: acc := by rfl

noncomputable def momentTypedRecord036 : MomentRecord :=
  { simplexId := 36,
    factorFloorsQ80 := #[(222774820267430054748 : Int), (253505866049427926924 : Int), (191646021074053602633 : Int), (574730573580592282353 : Int), (298532625073673972622 : Int), (461043602662049862350 : Int), (458162007143047251324 : Int), (731896767086553184672 : Int), (473759485151422698182 : Int), (473812065581362437508 : Int)],
    oldFloorQ96 := (5331673238862 : Int),
    newFloorQ96 := (5349962398152 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_036_before_decode"
  err.flush

theorem decode_moment_record_036 :
    decodeMomentRecord momentJsonRecord036 = .ok momentTypedRecord036 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_036_decoded"
  err.flush

noncomputable def momentJsonRecord037 : SourceJson :=
  (momentRecordsChunk037Push []).head (List.cons_ne_nil _ _)

theorem moment_record_037_push_eq (acc : List SourceJson) :
    momentRecordsChunk037Push acc = momentJsonRecord037 :: acc := by rfl

noncomputable def momentTypedRecord037 : MomentRecord :=
  { simplexId := 37,
    factorFloorsQ80 := #[(383308817855489086438 : Int), (432989664626154780521 : Int), (209816501032021789377 : Int), (577707959095179812841 : Int), (374457505899707833967 : Int), (494548499963133734292 : Int), (333759762489341285069 : Int), (735312610557315449385 : Int), (473828118629228602401 : Int), (473880472008412745003 : Int)],
    oldFloorQ96 := (5071544123641 : Int),
    newFloorQ96 := (5090413425656 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_037_before_decode"
  err.flush

theorem decode_moment_record_037 :
    decodeMomentRecord momentJsonRecord037 = .ok momentTypedRecord037 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_037_decoded"
  err.flush

noncomputable def momentJsonRecord038 : SourceJson :=
  (momentRecordsChunk038Push []).head (List.cons_ne_nil _ _)

theorem moment_record_038_push_eq (acc : List SourceJson) :
    momentRecordsChunk038Push acc = momentJsonRecord038 :: acc := by rfl

noncomputable def momentTypedRecord038 : MomentRecord :=
  { simplexId := 38,
    factorFloorsQ80 := #[(422379774952551335136 : Int), (477513864889271441811 : Int), (203217440035785087545 : Int), (454677358375681302622 : Int), (374776016494342991058 : Int), (453593977005062790122 : Int), (302282637576411520333 : Int), (621359179028318931336 : Int), (307361121614503528544 : Int), (307399006465641604828 : Int)],
    oldFloorQ96 := (3594482412759 : Int),
    newFloorQ96 := (3606170214719 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_038_before_decode"
  err.flush

theorem decode_moment_record_038 :
    decodeMomentRecord momentJsonRecord038 = .ok momentTypedRecord038 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_038_decoded"
  err.flush

noncomputable def momentJsonRecord039 : SourceJson :=
  (momentRecordsChunk039Push []).head (List.cons_ne_nil _ _)

theorem moment_record_039_push_eq (acc : List SourceJson) :
    momentRecordsChunk039Push acc = momentJsonRecord039 :: acc := by rfl

noncomputable def momentTypedRecord039 : MomentRecord :=
  { simplexId := 39,
    factorFloorsQ80 := #[(413784439929771744527 : Int), (478888830340149748575 : Int), (185757003036587134937 : Int), (395761802646248744400 : Int), (331679447624699320129 : Int), (391131119477553919745 : Int), (251575299470270191634 : Int), (469562911606542891388 : Int), (330595094633516631880 : Int), (330629054737543074907 : Int)],
    oldFloorQ96 := (2754749942414 : Int),
    newFloorQ96 := (2762918240926 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_039_before_decode"
  err.flush

theorem decode_moment_record_039 :
    decodeMomentRecord momentJsonRecord039 = .ok momentTypedRecord039 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_039_decoded"
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
  err.putStrLn "P26_MOMENT00 typed_block_009_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
