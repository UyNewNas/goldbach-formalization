import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock006
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock007

/-! Original typed moment records 28 through 31; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord028 : SourceJson :=
  (momentRecordsChunk028Push []).head (List.cons_ne_nil _ _)

theorem moment_record_028_push_eq (acc : List SourceJson) :
    momentRecordsChunk028Push acc = momentJsonRecord028 :: acc := by rfl

noncomputable def momentTypedRecord028 : MomentRecord :=
  { simplexId := 28,
    factorFloorsQ80 := #[(1458957581114772067807 : Int), (1596592304708207511059 : Int), (264200808788180271028 : Int), (373234141597672396938 : Int), (665190035568001631224 : Int), (1737250490096702888725 : Int), (1036095226060574467215 : Int), (1179444269384511065250 : Int), (1179498904807598268671 : Int), (1036581973256028408225 : Int)],
    oldFloorQ96 := (861503782172894 : Int),
    newFloorQ96 := (869038314023036 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_028_before_decode"
  err.flush

theorem decode_moment_record_028 :
    decodeMomentRecord momentJsonRecord028 = .ok momentTypedRecord028 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_028_decoded"
  err.flush

noncomputable def momentJsonRecord029 : SourceJson :=
  (momentRecordsChunk029Push []).head (List.cons_ne_nil _ _)

theorem moment_record_029_push_eq (acc : List SourceJson) :
    momentRecordsChunk029Push acc = momentJsonRecord029 :: acc := by rfl

noncomputable def momentTypedRecord029 : MomentRecord :=
  { simplexId := 29,
    factorFloorsQ80 := #[(1354882332698458616640 : Int), (1460184274969733756559 : Int), (268522303186478862393 : Int), (377016022616843543670 : Int), (768695329450031179574 : Int), (1802627164513449056283 : Int), (1682332701983534837557 : Int), (1260137479286503978346 : Int), (1260190056479605727150 : Int), (774139949092395396543 : Int)],
    oldFloorQ96 := (1068398991284423 : Int),
    newFloorQ96 := (1078172484523363 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_029_before_decode"
  err.flush

theorem decode_moment_record_029 :
    decodeMomentRecord momentJsonRecord029 = .ok momentTypedRecord029 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_029_decoded"
  err.flush

noncomputable def momentJsonRecord030 : SourceJson :=
  (momentRecordsChunk030Push []).head (List.cons_ne_nil _ _)

theorem moment_record_030_push_eq (acc : List SourceJson) :
    momentRecordsChunk030Push acc = momentJsonRecord030 :: acc := by rfl

noncomputable def momentTypedRecord030 : MomentRecord :=
  { simplexId := 30,
    factorFloorsQ80 := #[(1785139004940683836521 : Int), (1857393395148536151520 : Int), (286680669546059940575 : Int), (517001095526175022171 : Int), (751871604875206604938 : Int), (2051504410707547399482 : Int), (1811685080235620252860 : Int), (900251919935322545213 : Int), (910616911338314595345 : Int), (910620970749461506677 : Int)],
    oldFloorQ96 := (962561934549333 : Int),
    newFloorQ96 := (971989387435652 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_030_before_decode"
  err.flush

theorem decode_moment_record_030 :
    decodeMomentRecord momentJsonRecord030 = .ok momentTypedRecord030 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_030_decoded"
  err.flush

noncomputable def momentJsonRecord031 : SourceJson :=
  (momentRecordsChunk031Push []).head (List.cons_ne_nil _ _)

theorem moment_record_031_push_eq (acc : List SourceJson) :
    momentRecordsChunk031Push acc = momentJsonRecord031 :: acc := by rfl

noncomputable def momentTypedRecord031 : MomentRecord :=
  { simplexId := 31,
    factorFloorsQ80 := #[(1643312990408093744688 : Int), (1760834824704471004481 : Int), (272663811726215409070 : Int), (428397612364008940595 : Int), (756930810861365142042 : Int), (1743602581228496312574 : Int), (1773342879278939823441 : Int), (881743257199275213576 : Int), (919158923026322154104 : Int), (940913603736510380081 : Int)],
    oldFloorQ96 := (10640638812120361930 : Int),
    newFloorQ96 := (10738973577980089676 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_031_before_decode"
  err.flush

theorem decode_moment_record_031 :
    decodeMomentRecord momentJsonRecord031 = .ok momentTypedRecord031 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_031_decoded"
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
  err.putStrLn "P26_MOMENT01 typed_block_007_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
