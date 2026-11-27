import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock007
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock008

/-! Original typed moment records 32 through 35; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord032 : SourceJson :=
  (momentRecordsChunk032Push []).head (List.cons_ne_nil _ _)

theorem moment_record_032_push_eq (acc : List SourceJson) :
    momentRecordsChunk032Push acc = momentJsonRecord032 :: acc := by rfl

noncomputable def momentTypedRecord032 : MomentRecord :=
  { simplexId := 32,
    factorFloorsQ80 := #[(215470173103072492866 : Int), (272634018380087960640 : Int), (136974486434835259562 : Int), (227530557348399676927 : Int), (290162660675102782206 : Int), (306937366247152922431 : Int), (1316241524900112105314 : Int), (265864506612444835999 : Int), (316771767959068085186 : Int), (223142637213164260763 : Int)],
    oldFloorQ96 := (4478593021327850 : Int),
    newFloorQ96 := (4491844435938149 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_032_before_decode"
  err.flush

theorem decode_moment_record_032 :
    decodeMomentRecord momentJsonRecord032 = .ok momentTypedRecord032 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_032_decoded"
  err.flush

noncomputable def momentJsonRecord033 : SourceJson :=
  (momentRecordsChunk033Push []).head (List.cons_ne_nil _ _)

theorem moment_record_033_push_eq (acc : List SourceJson) :
    momentRecordsChunk033Push acc = momentJsonRecord033 :: acc := by rfl

noncomputable def momentTypedRecord033 : MomentRecord :=
  { simplexId := 33,
    factorFloorsQ80 := #[(172685237055928215032 : Int), (227732445350420756823 : Int), (82455845337604005616 : Int), (105711827157262793619 : Int), (197067902924216197892 : Int), (129207849250364582611 : Int), (635938430291319681289 : Int), (265172727637798974773 : Int), (298207422717691193546 : Int), (207295955868625394305 : Int)],
    oldFloorQ96 := (4969513484364300 : Int),
    newFloorQ96 := (4979065508293854 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_033_before_decode"
  err.flush

theorem decode_moment_record_033 :
    decodeMomentRecord momentJsonRecord033 = .ok momentTypedRecord033 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_033_decoded"
  err.flush

noncomputable def momentJsonRecord034 : SourceJson :=
  (momentRecordsChunk034Push []).head (List.cons_ne_nil _ _)

theorem moment_record_034_push_eq (acc : List SourceJson) :
    momentRecordsChunk034Push acc = momentJsonRecord034 :: acc := by rfl

noncomputable def momentTypedRecord034 : MomentRecord :=
  { simplexId := 34,
    factorFloorsQ80 := #[(332618792161650198567 : Int), (361210794260910661848 : Int), (176022483898475134433 : Int), (379434191428130444617 : Int), (412463474332177203140 : Int), (372972013964622152727 : Int), (1492820632752578122552 : Int), (297095481979287047801 : Int), (383806634642961741862 : Int), (218367590664271723641 : Int)],
    oldFloorQ96 := (1550208929780 : Int),
    newFloorQ96 := (1555895848933 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_034_before_decode"
  err.flush

theorem decode_moment_record_034 :
    decodeMomentRecord momentJsonRecord034 = .ok momentTypedRecord034 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_034_decoded"
  err.flush

noncomputable def momentJsonRecord035 : SourceJson :=
  (momentRecordsChunk035Push []).head (List.cons_ne_nil _ _)

theorem moment_record_035_push_eq (acc : List SourceJson) :
    momentRecordsChunk035Push acc = momentJsonRecord035 :: acc := by rfl

noncomputable def momentTypedRecord035 : MomentRecord :=
  { simplexId := 35,
    factorFloorsQ80 := #[(226975992053167912894 : Int), (271050001997847738755 : Int), (157968949220149447682 : Int), (287950000210017596276 : Int), (364508886561037599839 : Int), (324738046372539191295 : Int), (1482259801529427956807 : Int), (274545054674918099052 : Int), (344238576943566705637 : Int), (179025814530486881341 : Int)],
    oldFloorQ96 := (1076878139826 : Int),
    newFloorQ96 := (1080369613931 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_035_before_decode"
  err.flush

theorem decode_moment_record_035 :
    decodeMomentRecord momentJsonRecord035 = .ok momentTypedRecord035 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_035_decoded"
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
  err.putStrLn "P26_MOMENT05 typed_block_008_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
