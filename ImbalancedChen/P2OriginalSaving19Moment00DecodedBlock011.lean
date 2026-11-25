import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock010
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock011

/-! Original typed moment records 44 through 47; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord044 : SourceJson :=
  (momentRecordsChunk044Push []).head (List.cons_ne_nil _ _)

theorem moment_record_044_push_eq (acc : List SourceJson) :
    momentRecordsChunk044Push acc = momentJsonRecord044 :: acc := by rfl

noncomputable def momentTypedRecord044 : MomentRecord :=
  { simplexId := 44,
    factorFloorsQ80 := #[(157687032672607371203 : Int), (156633191055721102827 : Int), (145324234283429616010 : Int), (399390874348896624090 : Int), (190715000667741262499 : Int), (352662546373134752266 : Int), (489689262295500702094 : Int), (338244380151361392196 : Int), (343676362263402338873 : Int), (315859070711384374444 : Int)],
    oldFloorQ96 := (80584934695278519 : Int),
    newFloorQ96 := (80777799726573103 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_044_before_decode"
  err.flush

theorem decode_moment_record_044 :
    decodeMomentRecord momentJsonRecord044 = .ok momentTypedRecord044 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_044_decoded"
  err.flush

noncomputable def momentJsonRecord045 : SourceJson :=
  (momentRecordsChunk045Push []).head (List.cons_ne_nil _ _)

theorem moment_record_045_push_eq (acc : List SourceJson) :
    momentRecordsChunk045Push acc = momentJsonRecord045 :: acc := by rfl

noncomputable def momentTypedRecord045 : MomentRecord :=
  { simplexId := 45,
    factorFloorsQ80 := #[(177050320636749352082 : Int), (193568101762016856154 : Int), (144469059639348269992 : Int), (457421602773371012652 : Int), (190133072406520064470 : Int), (363596110907958928186 : Int), (500037339368030677368 : Int), (373264711780809731178 : Int), (422490826090961869734 : Int), (432787426506326875891 : Int)],
    oldFloorQ96 := (8373033008843 : Int),
    newFloorQ96 := (8395606290313 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_045_before_decode"
  err.flush

theorem decode_moment_record_045 :
    decodeMomentRecord momentJsonRecord045 = .ok momentTypedRecord045 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_045_decoded"
  err.flush

noncomputable def momentJsonRecord046 : SourceJson :=
  (momentRecordsChunk046Push []).head (List.cons_ne_nil _ _)

theorem moment_record_046_push_eq (acc : List SourceJson) :
    momentRecordsChunk046Push acc = momentJsonRecord046 :: acc := by rfl

noncomputable def momentTypedRecord046 : MomentRecord :=
  { simplexId := 46,
    factorFloorsQ80 := #[(153375179532481315839 : Int), (164213462788471773380 : Int), (144469059639348269992 : Int), (390836612867471224999 : Int), (190133072406520064470 : Int), (363596110907958928186 : Int), (500037339368030677368 : Int), (373264711780809731178 : Int), (363691076794220766775 : Int), (309844175824267188098 : Int)],
    oldFloorQ96 := (87417253456011073 : Int),
    newFloorQ96 := (87631078871154639 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_046_before_decode"
  err.flush

theorem decode_moment_record_046 :
    decodeMomentRecord momentJsonRecord046 = .ok momentTypedRecord046 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_046_decoded"
  err.flush

noncomputable def momentJsonRecord047 : SourceJson :=
  (momentRecordsChunk047Push []).head (List.cons_ne_nil _ _)

theorem moment_record_047_push_eq (acc : List SourceJson) :
    momentRecordsChunk047Push acc = momentJsonRecord047 :: acc := by rfl

noncomputable def momentTypedRecord047 : MomentRecord :=
  { simplexId := 47,
    factorFloorsQ80 := #[(125281171572598601805 : Int), (129320480749032846892 : Int), (141273028251287053524 : Int), (392490351321347289556 : Int), (197783907924480202946 : Int), (350486764770300602189 : Int), (627148429661225794102 : Int), (358670314597543752785 : Int), (249292672064446764952 : Int), (249319870060442081904 : Int)],
    oldFloorQ96 := (6419807225204 : Int),
    newFloorQ96 := (6434805543008 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_047_before_decode"
  err.flush

theorem decode_moment_record_047 :
    decodeMomentRecord momentJsonRecord047 = .ok momentTypedRecord047 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_047_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock011 : List SourceJson := [momentJsonRecord044, momentJsonRecord045, momentJsonRecord046, momentJsonRecord047]
noncomputable def momentTypedRecordsBlock011 : List MomentRecord := [momentTypedRecord044, momentTypedRecord045, momentTypedRecord046, momentTypedRecord047]

theorem moment_records_block_011_push_eq (acc : List SourceJson) :
    momentRecordsBlock011Push acc = [momentJsonRecord047, momentJsonRecord046, momentJsonRecord045, momentJsonRecord044] ++ acc := by rfl

theorem moment_records_block_011_reverse (acc : List SourceJson) :
    (momentRecordsBlock011Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock011 := by
  rw [moment_records_block_011_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_011 :
    momentJsonRecordsBlock011.mapM decodeMomentRecord = .ok momentTypedRecordsBlock011 := by
  simp only [momentJsonRecordsBlock011, momentTypedRecordsBlock011, List.mapM_cons, List.mapM_nil,
    decode_moment_record_044, decode_moment_record_045, decode_moment_record_046, decode_moment_record_047]
  rfl

noncomputable def momentTypedRowsThroughBlock011 : List MomentRecord := momentTypedRowsThroughBlock010 ++ momentTypedRecordsBlock011

theorem decode_moment_records_through_block_011 :
    momentRecordsAcc048.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock011 := by
  change (momentRecordsBlock011Push momentRecordsAcc044).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_011_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_010, decode_moment_records_block_011]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_block_011_complete"
  err.flush

#print axioms moment_record_044_push_eq
#print axioms decode_moment_record_044
#print axioms moment_record_045_push_eq
#print axioms decode_moment_record_045
#print axioms moment_record_046_push_eq
#print axioms decode_moment_record_046
#print axioms moment_record_047_push_eq
#print axioms decode_moment_record_047
#print axioms moment_records_block_011_push_eq
#print axioms moment_records_block_011_reverse
#print axioms decode_moment_records_block_011
#print axioms decode_moment_records_through_block_011

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
