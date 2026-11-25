import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock004
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock005

/-! Original typed moment records 20 through 23; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord020 : SourceJson :=
  (momentRecordsChunk020Push []).head (List.cons_ne_nil _ _)

theorem moment_record_020_push_eq (acc : List SourceJson) :
    momentRecordsChunk020Push acc = momentJsonRecord020 :: acc := by rfl

noncomputable def momentTypedRecord020 : MomentRecord :=
  { simplexId := 20,
    factorFloorsQ80 := #[(1472245972214294729717 : Int), (1530790585258971581547 : Int), (292017458515529913908 : Int), (492387670333777188072 : Int), (702069226553792444564 : Int), (2088655965906048436291 : Int), (1660873743011182791774 : Int), (1036785227677489771363 : Int), (543035273485456607911 : Int), (542997925559085558073 : Int)],
    oldFloorQ96 := (705420449982744 : Int),
    newFloorQ96 := (711492685221769 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_020_before_decode"
  err.flush

theorem decode_moment_record_020 :
    decodeMomentRecord momentJsonRecord020 = .ok momentTypedRecord020 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_020_decoded"
  err.flush

noncomputable def momentJsonRecord021 : SourceJson :=
  (momentRecordsChunk021Push []).head (List.cons_ne_nil _ _)

theorem moment_record_021_push_eq (acc : List SourceJson) :
    momentRecordsChunk021Push acc = momentJsonRecord021 :: acc := by rfl

noncomputable def momentTypedRecord021 : MomentRecord :=
  { simplexId := 21,
    factorFloorsQ80 := #[(1350640791888904600665 : Int), (1445993667281060700047 : Int), (277620778133104166990 : Int), (378044683620567424982 : Int), (701067104361951875813 : Int), (1761712698648001601636 : Int), (1624470894315701635203 : Int), (1030799227294510756256 : Int), (606853188245341599359 : Int), (519281658437906338964 : Int)],
    oldFloorQ96 := (7798112395442014296 : Int),
    newFloorQ96 := (7860910565822836086 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_021_before_decode"
  err.flush

theorem decode_moment_record_021 :
    decodeMomentRecord momentJsonRecord021 = .ok momentTypedRecord021 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_021_decoded"
  err.flush

noncomputable def momentJsonRecord022 : SourceJson :=
  (momentRecordsChunk022Push []).head (List.cons_ne_nil _ _)

theorem moment_record_022_push_eq (acc : List SourceJson) :
    momentRecordsChunk022Push acc = momentJsonRecord022 :: acc := by rfl

noncomputable def momentTypedRecord022 : MomentRecord :=
  { simplexId := 22,
    factorFloorsQ80 := #[(1333177734773639581379 : Int), (1396515858322254076837 : Int), (268103713123032962621 : Int), (390397469476290098409 : Int), (728427962953321945937 : Int), (1762175269325517708675 : Int), (1565317187989349553521 : Int), (1091834433887711183588 : Int), (808979892553317687370 : Int), (542214115891543954293 : Int)],
    oldFloorQ96 := (11511065041431694013 : Int),
    newFloorQ96 := (11605593772347357986 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_022_before_decode"
  err.flush

theorem decode_moment_record_022 :
    decodeMomentRecord momentJsonRecord022 = .ok momentTypedRecord022 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_022_decoded"
  err.flush

noncomputable def momentJsonRecord023 : SourceJson :=
  (momentRecordsChunk023Push []).head (List.cons_ne_nil _ _)

theorem moment_record_023_push_eq (acc : List SourceJson) :
    momentRecordsChunk023Push acc = momentJsonRecord023 :: acc := by rfl

noncomputable def momentTypedRecord023 : MomentRecord :=
  { simplexId := 23,
    factorFloorsQ80 := #[(1327824770351927259610 : Int), (1413497169062426815552 : Int), (268103842919226392639 : Int), (372955161232815555313 : Int), (768425332402239247242 : Int), (1830512130868303842438 : Int), (1566649313130671574216 : Int), (1138892055838689559999 : Int), (1031240309720107363349 : Int), (649395522741780366805 : Int)],
    oldFloorQ96 := (18618761367267288538 : Int),
    newFloorQ96 := (18779118588355049417 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_023_before_decode"
  err.flush

theorem decode_moment_record_023 :
    decodeMomentRecord momentJsonRecord023 = .ok momentTypedRecord023 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_023_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock005 : List SourceJson := [momentJsonRecord020, momentJsonRecord021, momentJsonRecord022, momentJsonRecord023]
noncomputable def momentTypedRecordsBlock005 : List MomentRecord := [momentTypedRecord020, momentTypedRecord021, momentTypedRecord022, momentTypedRecord023]

theorem moment_records_block_005_push_eq (acc : List SourceJson) :
    momentRecordsBlock005Push acc = [momentJsonRecord023, momentJsonRecord022, momentJsonRecord021, momentJsonRecord020] ++ acc := by rfl

theorem moment_records_block_005_reverse (acc : List SourceJson) :
    (momentRecordsBlock005Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock005 := by
  rw [moment_records_block_005_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_005 :
    momentJsonRecordsBlock005.mapM decodeMomentRecord = .ok momentTypedRecordsBlock005 := by
  simp only [momentJsonRecordsBlock005, momentTypedRecordsBlock005, List.mapM_cons, List.mapM_nil,
    decode_moment_record_020, decode_moment_record_021, decode_moment_record_022, decode_moment_record_023]
  rfl

noncomputable def momentTypedRowsThroughBlock005 : List MomentRecord := momentTypedRowsThroughBlock004 ++ momentTypedRecordsBlock005

theorem decode_moment_records_through_block_005 :
    momentRecordsAcc024.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock005 := by
  change (momentRecordsBlock005Push momentRecordsAcc020).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_005_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_004, decode_moment_records_block_005]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_005_complete"
  err.flush

#print axioms moment_record_020_push_eq
#print axioms decode_moment_record_020
#print axioms moment_record_021_push_eq
#print axioms decode_moment_record_021
#print axioms moment_record_022_push_eq
#print axioms decode_moment_record_022
#print axioms moment_record_023_push_eq
#print axioms decode_moment_record_023
#print axioms moment_records_block_005_push_eq
#print axioms moment_records_block_005_reverse
#print axioms decode_moment_records_block_005
#print axioms decode_moment_records_through_block_005

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
