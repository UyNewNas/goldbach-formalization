import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock006
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock007

/-! Original typed moment records 28 through 31; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord028 : SourceJson :=
  (momentRecordsChunk028Push []).head (List.cons_ne_nil _ _)

theorem moment_record_028_push_eq (acc : List SourceJson) :
    momentRecordsChunk028Push acc = momentJsonRecord028 :: acc := by rfl

noncomputable def momentTypedRecord028 : MomentRecord :=
  { simplexId := 28,
    factorFloorsQ80 := #[(413673588747297928164 : Int), (479870400129285432121 : Int), (179660099692447060849 : Int), (362226095026463458628 : Int), (354954831383124831424 : Int), (347210213402183828355 : Int), (304866444595982763104 : Int), (391627303507496704212 : Int), (516127277549024434226 : Int), (359250185528427258756 : Int)],
    oldFloorQ96 := (50317923500938118 : Int),
    newFloorQ96 := (50472556068766105 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_028_before_decode"
  err.flush

theorem decode_moment_record_028 :
    decodeMomentRecord momentJsonRecord028 = .ok momentTypedRecord028 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_028_decoded"
  err.flush

noncomputable def momentJsonRecord029 : SourceJson :=
  (momentRecordsChunk029Push []).head (List.cons_ne_nil _ _)

theorem moment_record_029_push_eq (acc : List SourceJson) :
    momentRecordsChunk029Push acc = momentJsonRecord029 :: acc := by rfl

noncomputable def momentTypedRecord029 : MomentRecord :=
  { simplexId := 29,
    factorFloorsQ80 := #[(268340582209103236195 : Int), (359391519525226789760 : Int), (141175161709767729385 : Int), (202563305233220242282 : Int), (300898971035029097200 : Int), (188752062798723285040 : Int), (309444950286078822023 : Int), (382102729755031969044 : Int), (497270029364605561192 : Int), (290982973944474300560 : Int)],
    oldFloorQ96 := (34013559601133510 : Int),
    newFloorQ96 := (34096404225822403 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_029_before_decode"
  err.flush

theorem decode_moment_record_029 :
    decodeMomentRecord momentJsonRecord029 = .ok momentTypedRecord029 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_029_decoded"
  err.flush

noncomputable def momentJsonRecord030 : SourceJson :=
  (momentRecordsChunk030Push []).head (List.cons_ne_nil _ _)

theorem moment_record_030_push_eq (acc : List SourceJson) :
    momentRecordsChunk030Push acc = momentJsonRecord030 :: acc := by rfl

noncomputable def momentTypedRecord030 : MomentRecord :=
  { simplexId := 30,
    factorFloorsQ80 := #[(200579809618628796382 : Int), (302595989939516152453 : Int), (105928623307997074600 : Int), (94814126198829822164 : Int), (193358542107490400360 : Int), (120997175526860708406 : Int), (243257125752235006366 : Int), (267450958632455882324 : Int), (350400930441012051161 : Int), (256515275174843904563 : Int)],
    oldFloorQ96 := (32822251023042827 : Int),
    newFloorQ96 := (32880291776049650 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_030_before_decode"
  err.flush

theorem decode_moment_record_030 :
    decodeMomentRecord momentJsonRecord030 = .ok momentTypedRecord030 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_030_decoded"
  err.flush

noncomputable def momentJsonRecord031 : SourceJson :=
  (momentRecordsChunk031Push []).head (List.cons_ne_nil _ _)

theorem moment_record_031_push_eq (acc : List SourceJson) :
    momentRecordsChunk031Push acc = momentJsonRecord031 :: acc := by rfl

noncomputable def momentTypedRecord031 : MomentRecord :=
  { simplexId := 31,
    factorFloorsQ80 := #[(506461452881267953760 : Int), (563188214300020482018 : Int), (209816501032021789377 : Int), (537052093636336123548 : Int), (434197105531159562166 : Int), (494548499963133734292 : Int), (372667496924618515472 : Int), (571013653831522418177 : Int), (369740875779456039377 : Int), (369800453445048357748 : Int)],
    oldFloorQ96 := (5030765930380 : Int),
    newFloorQ96 := (5049228215544 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_031_before_decode"
  err.flush

theorem decode_moment_record_031 :
    decodeMomentRecord momentJsonRecord031 = .ok momentTypedRecord031 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_031_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock007 : List SourceJson := [momentJsonRecord028, momentJsonRecord029, momentJsonRecord030, momentJsonRecord031]
noncomputable def momentTypedRecordsBlock007 : List MomentRecord := [momentTypedRecord028, momentTypedRecord029, momentTypedRecord030, momentTypedRecord031]

theorem moment_records_block_007_push_eq (acc : List SourceJson) :
    momentRecordsBlock007Push acc = [momentJsonRecord031, momentJsonRecord030, momentJsonRecord029, momentJsonRecord028] ++ acc := by rfl

theorem moment_records_block_007_reverse (acc : List SourceJson) :
    (momentRecordsBlock007Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock007 := by
  rw [moment_records_block_007_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_007 :
    momentJsonRecordsBlock007.mapM decodeMomentRecord = .ok momentTypedRecordsBlock007 := by
  simp only [momentJsonRecordsBlock007, momentTypedRecordsBlock007, List.mapM_cons, List.mapM_nil,
    decode_moment_record_028, decode_moment_record_029, decode_moment_record_030, decode_moment_record_031]
  rfl

noncomputable def momentTypedRowsThroughBlock007 : List MomentRecord := momentTypedRowsThroughBlock006 ++ momentTypedRecordsBlock007

theorem decode_moment_records_through_block_007 :
    momentRecordsAcc032.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock007 := by
  change (momentRecordsBlock007Push momentRecordsAcc028).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_007_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_006, decode_moment_records_block_007]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_block_007_complete"
  err.flush

#print axioms moment_record_028_push_eq
#print axioms decode_moment_record_028
#print axioms moment_record_029_push_eq
#print axioms decode_moment_record_029
#print axioms moment_record_030_push_eq
#print axioms decode_moment_record_030
#print axioms moment_record_031_push_eq
#print axioms decode_moment_record_031
#print axioms moment_records_block_007_push_eq
#print axioms moment_records_block_007_reverse
#print axioms decode_moment_records_block_007
#print axioms decode_moment_records_through_block_007

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
