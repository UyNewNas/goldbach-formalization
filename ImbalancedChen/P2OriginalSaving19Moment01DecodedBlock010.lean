import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock009
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock010

/-! Original typed moment records 40 through 43; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord040 : SourceJson :=
  (momentRecordsChunk040Push []).head (List.cons_ne_nil _ _)

theorem moment_record_040_push_eq (acc : List SourceJson) :
    momentRecordsChunk040Push acc = momentJsonRecord040 :: acc := by rfl

noncomputable def momentTypedRecord040 : MomentRecord :=
  { simplexId := 40,
    factorFloorsQ80 := #[(2196220700669862879689 : Int), (2428614694323968612900 : Int), (268284496885779846050 : Int), (548878425996730131714 : Int), (995646293807785943490 : Int), (1618315680907721065632 : Int), (1392840800587838557033 : Int), (1124982323921566813317 : Int), (1249618739736535783676 : Int), (1406859967719044004179 : Int)],
    oldFloorQ96 := (490231038210423539 : Int),
    newFloorQ96 := (495625500521593111 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_040_before_decode"
  err.flush

theorem decode_moment_record_040 :
    decodeMomentRecord momentJsonRecord040 = .ok momentTypedRecord040 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_040_decoded"
  err.flush

noncomputable def momentJsonRecord041 : SourceJson :=
  (momentRecordsChunk041Push []).head (List.cons_ne_nil _ _)

theorem moment_record_041_push_eq (acc : List SourceJson) :
    momentRecordsChunk041Push acc = momentJsonRecord041 :: acc := by rfl

noncomputable def momentTypedRecord041 : MomentRecord :=
  { simplexId := 41,
    factorFloorsQ80 := #[(2133538438236166489555 : Int), (2292990152092536882962 : Int), (257879721996756954218 : Int), (548683931334781120628 : Int), (991848051645077827744 : Int), (1617855505282233264684 : Int), (1336134955851422070481 : Int), (1082547526645394386636 : Int), (1082727788620391165587 : Int), (1574228188279601107902 : Int)],
    oldFloorQ96 := (726840489500129520 : Int),
    newFloorQ96 := (734649064605866098 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_041_before_decode"
  err.flush

theorem decode_moment_record_041 :
    decodeMomentRecord momentJsonRecord041 = .ok momentTypedRecord041 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_041_decoded"
  err.flush

noncomputable def momentJsonRecord042 : SourceJson :=
  (momentRecordsChunk042Push []).head (List.cons_ne_nil _ _)

theorem moment_record_042_push_eq (acc : List SourceJson) :
    momentRecordsChunk042Push acc = momentJsonRecord042 :: acc := by rfl

noncomputable def momentTypedRecord042 : MomentRecord :=
  { simplexId := 42,
    factorFloorsQ80 := #[(2731932932480773285180 : Int), (2915789068718379513504 : Int), (277056638067324117480 : Int), (658808951760640710638 : Int), (1152622688583465998641 : Int), (2013926874841040790479 : Int), (1589811999135674305784 : Int), (1358457501712236413017 : Int), (1419486420956087917085 : Int), (1419563662281869463452 : Int)],
    oldFloorQ96 := (10168429982070 : Int),
    newFloorQ96 := (10299960936162 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_042_before_decode"
  err.flush

theorem decode_moment_record_042 :
    decodeMomentRecord momentJsonRecord042 = .ok momentTypedRecord042 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_042_decoded"
  err.flush

noncomputable def momentJsonRecord043 : SourceJson :=
  (momentRecordsChunk043Push []).head (List.cons_ne_nil _ _)

theorem moment_record_043_push_eq (acc : List SourceJson) :
    momentRecordsChunk043Push acc = momentJsonRecord043 :: acc := by rfl

noncomputable def momentTypedRecord043 : MomentRecord :=
  { simplexId := 43,
    factorFloorsQ80 := #[(2354184624539919865341 : Int), (2658469049993299475084 : Int), (261450990540201812766 : Int), (599736132745608548630 : Int), (1142653219404230718880 : Int), (1618135121240369616730 : Int), (1530544729409798253734 : Int), (1298660214068855751175 : Int), (1292902298690745481877 : Int), (1509834609260215855018 : Int)],
    oldFloorQ96 := (103913806105074141 : Int),
    newFloorQ96 := (105147360351443591 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_043_before_decode"
  err.flush

theorem decode_moment_record_043 :
    decodeMomentRecord momentJsonRecord043 = .ok momentTypedRecord043 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_043_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock010 : List SourceJson := [momentJsonRecord040, momentJsonRecord041, momentJsonRecord042, momentJsonRecord043]
noncomputable def momentTypedRecordsBlock010 : List MomentRecord := [momentTypedRecord040, momentTypedRecord041, momentTypedRecord042, momentTypedRecord043]

theorem moment_records_block_010_push_eq (acc : List SourceJson) :
    momentRecordsBlock010Push acc = [momentJsonRecord043, momentJsonRecord042, momentJsonRecord041, momentJsonRecord040] ++ acc := by rfl

theorem moment_records_block_010_reverse (acc : List SourceJson) :
    (momentRecordsBlock010Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock010 := by
  rw [moment_records_block_010_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_010 :
    momentJsonRecordsBlock010.mapM decodeMomentRecord = .ok momentTypedRecordsBlock010 := by
  simp only [momentJsonRecordsBlock010, momentTypedRecordsBlock010, List.mapM_cons, List.mapM_nil,
    decode_moment_record_040, decode_moment_record_041, decode_moment_record_042, decode_moment_record_043]
  rfl

noncomputable def momentTypedRowsThroughBlock010 : List MomentRecord := momentTypedRowsThroughBlock009 ++ momentTypedRecordsBlock010

theorem decode_moment_records_through_block_010 :
    momentRecordsAcc044.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock010 := by
  change (momentRecordsBlock010Push momentRecordsAcc040).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_010_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_009, decode_moment_records_block_010]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_010_complete"
  err.flush

#print axioms moment_record_040_push_eq
#print axioms decode_moment_record_040
#print axioms moment_record_041_push_eq
#print axioms decode_moment_record_041
#print axioms moment_record_042_push_eq
#print axioms decode_moment_record_042
#print axioms moment_record_043_push_eq
#print axioms decode_moment_record_043
#print axioms moment_records_block_010_push_eq
#print axioms moment_records_block_010_reverse
#print axioms decode_moment_records_block_010
#print axioms decode_moment_records_through_block_010

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
