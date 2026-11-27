import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock004
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock005

/-! Original typed moment records 20 through 23; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord020 : SourceJson :=
  (momentRecordsChunk020Push []).head (List.cons_ne_nil _ _)

theorem moment_record_020_push_eq (acc : List SourceJson) :
    momentRecordsChunk020Push acc = momentJsonRecord020 :: acc := by rfl

noncomputable def momentTypedRecord020 : MomentRecord :=
  { simplexId := 20,
    factorFloorsQ80 := #[(362162878541258257019 : Int), (397160117874600107217 : Int), (177157062887978885243 : Int), (378402113392558893102 : Int), (392514646868234456173 : Int), (355290385469429682223 : Int), (1219951904601661792311 : Int), (273882476974790226509 : Int), (265133145040315992448 : Int), (223426307632548541952 : Int)],
    oldFloorQ96 := (5996607507367378 : Int),
    newFloorQ96 := (6016705837566120 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_020_before_decode"
  err.flush

theorem decode_moment_record_020 :
    decodeMomentRecord momentJsonRecord020 = .ok momentTypedRecord020 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_020_decoded"
  err.flush

noncomputable def momentJsonRecord021 : SourceJson :=
  (momentRecordsChunk021Push []).head (List.cons_ne_nil _ _)

theorem moment_record_021_push_eq (acc : List SourceJson) :
    momentRecordsChunk021Push acc = momentJsonRecord021 :: acc := by rfl

noncomputable def momentTypedRecord021 : MomentRecord :=
  { simplexId := 21,
    factorFloorsQ80 := #[(359623378927006973250 : Int), (381000839779766247137 : Int), (175089242981242849105 : Int), (400951105427577460707 : Int), (403073842793920060456 : Int), (360185489951176277525 : Int), (1213080951832378317812 : Int), (307668448257400817309 : Int), (351425381301150792273 : Int), (214661459837959097859 : Int)],
    oldFloorQ96 := (7877674323083078 : Int),
    newFloorQ96 := (7904872858444145 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_021_before_decode"
  err.flush

theorem decode_moment_record_021 :
    decodeMomentRecord momentJsonRecord021 = .ok momentTypedRecord021 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_021_decoded"
  err.flush

noncomputable def momentJsonRecord022 : SourceJson :=
  (momentRecordsChunk022Push []).head (List.cons_ne_nil _ _)

theorem moment_record_022_push_eq (acc : List SourceJson) :
    momentRecordsChunk022Push acc = momentJsonRecord022 :: acc := by rfl

noncomputable def momentTypedRecord022 : MomentRecord :=
  { simplexId := 22,
    factorFloorsQ80 := #[(276879861471311549464 : Int), (317156234222372164290 : Int), (182697373552958600652 : Int), (373763288286513727837 : Int), (376700555670179359362 : Int), (426250008336500235641 : Int), (1678866087020959025302 : Int), (267554668363282986881 : Int), (192632076244863215311 : Int), (192635908414646800350 : Int)],
    oldFloorQ96 := (819342764849 : Int),
    newFloorQ96 := (822252145249 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_022_before_decode"
  err.flush

theorem decode_moment_record_022 :
    decodeMomentRecord momentJsonRecord022 = .ok momentTypedRecord022 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_022_decoded"
  err.flush

noncomputable def momentJsonRecord023 : SourceJson :=
  (momentRecordsChunk023Push []).head (List.cons_ne_nil _ _)

theorem moment_record_023_push_eq (acc : List SourceJson) :
    momentRecordsChunk023Push acc = momentJsonRecord023 :: acc := by rfl

noncomputable def momentTypedRecord023 : MomentRecord :=
  { simplexId := 23,
    factorFloorsQ80 := #[(274675052697324675793 : Int), (329155534000422852709 : Int), (170226955370840850644 : Int), (309826706503261173402 : Int), (380617688939629275976 : Int), (331185800013694483711 : Int), (1216649311289378135999 : Int), (266064783563457877269 : Int), (258596331090203632927 : Int), (198494381490219460381 : Int)],
    oldFloorQ96 := (4351178395486052 : Int),
    newFloorQ96 := (4364644012298532 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_023_before_decode"
  err.flush

theorem decode_moment_record_023 :
    decodeMomentRecord momentJsonRecord023 = .ok momentTypedRecord023 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_023_decoded"
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
  err.putStrLn "P26_MOMENT05 typed_block_005_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
