import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock001
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock002

/-! Original typed moment records 8 through 11; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord008 : SourceJson :=
  (momentRecordsChunk008Push []).head (List.cons_ne_nil _ _)

theorem moment_record_008_push_eq (acc : List SourceJson) :
    momentRecordsChunk008Push acc = momentJsonRecord008 :: acc := by rfl

noncomputable def momentTypedRecord008 : MomentRecord :=
  { simplexId := 8,
    factorFloorsQ80 := #[(334446425792084069350 : Int), (370921191373096474137 : Int), (198515890662594029056 : Int), (523992605373938855460 : Int), (336851075741343376437 : Int), (454981655190541380004 : Int), (340456979793085722940 : Int), (564164553361682124929 : Int), (548851835259113897242 : Int), (413004764762941559455 : Int)],
    oldFloorQ96 := (60345249796045797 : Int),
    newFloorQ96 := (60549562719722224 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_008_before_decode"
  err.flush

theorem decode_moment_record_008 :
    decodeMomentRecord momentJsonRecord008 = .ok momentTypedRecord008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_008_decoded"
  err.flush

noncomputable def momentJsonRecord009 : SourceJson :=
  (momentRecordsChunk009Push []).head (List.cons_ne_nil _ _)

theorem moment_record_009_push_eq (acc : List SourceJson) :
    momentRecordsChunk009Push acc = momentJsonRecord009 :: acc := by rfl

noncomputable def momentTypedRecord009 : MomentRecord :=
  { simplexId := 9,
    factorFloorsQ80 := #[(344859499942540702994 : Int), (397231395523282441417 : Int), (197258836913267590509 : Int), (608836016240224144026 : Int), (352499523443183316395 : Int), (480660894452008337387 : Int), (370856702455468695322 : Int), (611613148218545790061 : Int), (618662311303536762781 : Int), (581277253414746459905 : Int)],
    oldFloorQ96 := (6264181415321 : Int),
    newFloorQ96 := (6287873705839 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_009_before_decode"
  err.flush

theorem decode_moment_record_009 :
    decodeMomentRecord momentJsonRecord009 = .ok momentTypedRecord009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_009_decoded"
  err.flush

noncomputable def momentJsonRecord010 : SourceJson :=
  (momentRecordsChunk010Push []).head (List.cons_ne_nil _ _)

theorem moment_record_010_push_eq (acc : List SourceJson) :
    momentRecordsChunk010Push acc = momentJsonRecord010 :: acc := by rfl

noncomputable def momentTypedRecord010 : MomentRecord :=
  { simplexId := 10,
    factorFloorsQ80 := #[(352381717591008640505 : Int), (397720290721908889524 : Int), (197258836913267590509 : Int), (523131637231449012446 : Int), (352499523443183316395 : Int), (480660894452008337387 : Int), (370856702455468695322 : Int), (611613148218545790061 : Int), (522417477961926415495 : Int), (414887560502602075468 : Int)],
    oldFloorQ96 := (65421830024762350 : Int),
    newFloorQ96 := (65650783342141174 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_010_before_decode"
  err.flush

theorem decode_moment_record_010 :
    decodeMomentRecord momentJsonRecord010 = .ok momentTypedRecord010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_010_decoded"
  err.flush

noncomputable def momentJsonRecord011 : SourceJson :=
  (momentRecordsChunk011Push []).head (List.cons_ne_nil _ _)

theorem moment_record_011_push_eq (acc : List SourceJson) :
    momentRecordsChunk011Push acc = momentJsonRecord011 :: acc := by rfl

noncomputable def momentTypedRecord011 : MomentRecord :=
  { simplexId := 11,
    factorFloorsQ80 := #[(459640207200725545711 : Int), (502561940377587738627 : Int), (212735523537510255068 : Int), (502075116963743340697 : Int), (369731313233774511987 : Int), (509131186216144579672 : Int), (294195519166110115299 : Int), (464091358841444047189 : Int), (505219852181963426272 : Int), (305482965810191653649 : Int)],
    oldFloorQ96 := (4500655802398 : Int),
    newFloorQ96 := (4516038305213 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_011_before_decode"
  err.flush

theorem decode_moment_record_011 :
    decodeMomentRecord momentJsonRecord011 = .ok momentTypedRecord011 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_011_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock002 : List SourceJson := [momentJsonRecord008, momentJsonRecord009, momentJsonRecord010, momentJsonRecord011]
noncomputable def momentTypedRecordsBlock002 : List MomentRecord := [momentTypedRecord008, momentTypedRecord009, momentTypedRecord010, momentTypedRecord011]

theorem moment_records_block_002_push_eq (acc : List SourceJson) :
    momentRecordsBlock002Push acc = [momentJsonRecord011, momentJsonRecord010, momentJsonRecord009, momentJsonRecord008] ++ acc := by rfl

theorem moment_records_block_002_reverse (acc : List SourceJson) :
    (momentRecordsBlock002Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock002 := by
  rw [moment_records_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_002 :
    momentJsonRecordsBlock002.mapM decodeMomentRecord = .ok momentTypedRecordsBlock002 := by
  simp only [momentJsonRecordsBlock002, momentTypedRecordsBlock002, List.mapM_cons, List.mapM_nil,
    decode_moment_record_008, decode_moment_record_009, decode_moment_record_010, decode_moment_record_011]
  rfl

noncomputable def momentTypedRowsThroughBlock002 : List MomentRecord := momentTypedRowsThroughBlock001 ++ momentTypedRecordsBlock002

theorem decode_moment_records_through_block_002 :
    momentRecordsAcc012.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock002 := by
  change (momentRecordsBlock002Push momentRecordsAcc008).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_002_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_001, decode_moment_records_block_002]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_block_002_complete"
  err.flush

#print axioms moment_record_008_push_eq
#print axioms decode_moment_record_008
#print axioms moment_record_009_push_eq
#print axioms decode_moment_record_009
#print axioms moment_record_010_push_eq
#print axioms decode_moment_record_010
#print axioms moment_record_011_push_eq
#print axioms decode_moment_record_011
#print axioms moment_records_block_002_push_eq
#print axioms moment_records_block_002_reverse
#print axioms decode_moment_records_block_002
#print axioms decode_moment_records_through_block_002

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
