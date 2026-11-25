import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock007
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock008

/-! Original typed moment records 32 through 35; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord032 : SourceJson :=
  (momentRecordsChunk032Push []).head (List.cons_ne_nil _ _)

theorem moment_record_032_push_eq (acc : List SourceJson) :
    momentRecordsChunk032Push acc = momentJsonRecord032 :: acc := by rfl

noncomputable def momentTypedRecord032 : MomentRecord :=
  { simplexId := 32,
    factorFloorsQ80 := #[(540970121419715054860 : Int), (603395065615170403673 : Int), (203217440035785087545 : Int), (426505605314407475561 : Int), (422411012852191391530 : Int), (453593977005062790122 : Int), (320340444306884491491 : Int), (477406273027819910311 : Int), (250876186563293864104 : Int), (250914053568454725151 : Int)],
    oldFloorQ96 := (3562708942954 : Int),
    newFloorQ96 := (3574367552254 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_032_before_decode"
  err.flush

theorem decode_moment_record_032 :
    decodeMomentRecord momentJsonRecord032 = .ok momentTypedRecord032 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_032_decoded"
  err.flush

noncomputable def momentJsonRecord033 : SourceJson :=
  (momentRecordsChunk033Push []).head (List.cons_ne_nil _ _)

theorem moment_record_033_push_eq (acc : List SourceJson) :
    momentRecordsChunk033Push acc = momentJsonRecord033 :: acc := by rfl

noncomputable def momentTypedRecord033 : MomentRecord :=
  { simplexId := 33,
    factorFloorsQ80 := #[(523631174135335194464 : Int), (596455262475596262396 : Int), (185757003036587134937 : Int), (374562416341975690322 : Int), (368600452738484197869 : Int), (391131119477553919745 : Int), (244154042963815976286 : Int), (350616872106605872962 : Int), (287075726250869640672 : Int), (287107709026561585830 : Int)],
    oldFloorQ96 := (2730226020247 : Int),
    newFloorQ96 := (2738388935737 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_033_before_decode"
  err.flush

theorem decode_moment_record_033 :
    decodeMomentRecord momentJsonRecord033 = .ok momentTypedRecord033 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_033_decoded"
  err.flush

noncomputable def momentJsonRecord034 : SourceJson :=
  (momentRecordsChunk034Push []).head (List.cons_ne_nil _ _)

theorem moment_record_034_push_eq (acc : List SourceJson) :
    momentRecordsChunk034Push acc = momentJsonRecord034 :: acc := by rfl

noncomputable def momentTypedRecord034 : MomentRecord :=
  { simplexId := 34,
    factorFloorsQ80 := #[(458040250905070364386 : Int), (543868061172126124165 : Int), (160322990055090657241 : Int), (286900412115518195350 : Int), (324555961948547650471 : Int), (341714299981790945597 : Int), (267894966989532113269 : Int), (311141046995686629393 : Int), (289354158973550021069 : Int), (289378674533731318762 : Int)],
    oldFloorQ96 := (2732140349073 : Int),
    newFloorQ96 := (2739547651603 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_034_before_decode"
  err.flush

theorem decode_moment_record_034 :
    decodeMomentRecord momentJsonRecord034 = .ok momentTypedRecord034 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_034_decoded"
  err.flush

noncomputable def momentJsonRecord035 : SourceJson :=
  (momentRecordsChunk035Push []).head (List.cons_ne_nil _ _)

theorem moment_record_035_push_eq (acc : List SourceJson) :
    momentRecordsChunk035Push acc = momentJsonRecord035 :: acc := by rfl

noncomputable def momentTypedRecord035 : MomentRecord :=
  { simplexId := 35,
    factorFloorsQ80 := #[(276011233364343690110 : Int), (380896523436991491361 : Int), (106426201195992490154 : Int), (110439474338349857277 : Int), (218384103224180533698 : Int), (135234486421348114138 : Int), (257774935286137305198 : Int), (275534781149612793508 : Int), (212438937719337070046 : Int), (212451761478187883769 : Int)],
    oldFloorQ96 := (2321600314409 : Int),
    newFloorQ96 := (2325801284748 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_035_before_decode"
  err.flush

theorem decode_moment_record_035 :
    decodeMomentRecord momentJsonRecord035 = .ok momentTypedRecord035 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_035_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock008 : List SourceJson := [momentJsonRecord032, momentJsonRecord033, momentJsonRecord034, momentJsonRecord035]
noncomputable def momentTypedRecordsBlock008 : List MomentRecord := [momentTypedRecord032, momentTypedRecord033, momentTypedRecord034, momentTypedRecord035]

theorem moment_records_block_008_push_eq (acc : List SourceJson) :
    momentRecordsBlock008Push acc = [momentJsonRecord035, momentJsonRecord034, momentJsonRecord033, momentJsonRecord032] ++ acc := by rfl

theorem moment_records_block_008_reverse (acc : List SourceJson) :
    (momentRecordsBlock008Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock008 := by
  rw [moment_records_block_008_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_008 :
    momentJsonRecordsBlock008.mapM decodeMomentRecord = .ok momentTypedRecordsBlock008 := by
  simp only [momentJsonRecordsBlock008, momentTypedRecordsBlock008, List.mapM_cons, List.mapM_nil,
    decode_moment_record_032, decode_moment_record_033, decode_moment_record_034, decode_moment_record_035]
  rfl

noncomputable def momentTypedRowsThroughBlock008 : List MomentRecord := momentTypedRowsThroughBlock007 ++ momentTypedRecordsBlock008

theorem decode_moment_records_through_block_008 :
    momentRecordsAcc036.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock008 := by
  change (momentRecordsBlock008Push momentRecordsAcc032).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_008_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_007, decode_moment_records_block_008]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_block_008_complete"
  err.flush

#print axioms moment_record_032_push_eq
#print axioms decode_moment_record_032
#print axioms moment_record_033_push_eq
#print axioms decode_moment_record_033
#print axioms moment_record_034_push_eq
#print axioms decode_moment_record_034
#print axioms moment_record_035_push_eq
#print axioms decode_moment_record_035
#print axioms moment_records_block_008_push_eq
#print axioms moment_records_block_008_reverse
#print axioms decode_moment_records_block_008
#print axioms decode_moment_records_through_block_008

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
