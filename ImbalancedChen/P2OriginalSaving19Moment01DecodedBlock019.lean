import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock018
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock019

/-! Original typed moment records 76 through 79; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord076 : SourceJson :=
  (momentRecordsChunk076Push []).head (List.cons_ne_nil _ _)

theorem moment_record_076_push_eq (acc : List SourceJson) :
    momentRecordsChunk076Push acc = momentJsonRecord076 :: acc := by rfl

noncomputable def momentTypedRecord076 : MomentRecord :=
  { simplexId := 76,
    factorFloorsQ80 := #[(1239056427189380858287 : Int), (1240727769110033709510 : Int), (112499596024753454651 : Int), (600430215657155511553 : Int), (1272170929918248631906 : Int), (1138382349017229600137 : Int), (900671448104962893355 : Int), (804659779845165253567 : Int), (721470942511620069759 : Int), (721544927672433914583 : Int)],
    oldFloorQ96 := (37511719418 : Int),
    newFloorQ96 := (37784258254 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_076_before_decode"
  err.flush

theorem decode_moment_record_076 :
    decodeMomentRecord momentJsonRecord076 = .ok momentTypedRecord076 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_076_decoded"
  err.flush

noncomputable def momentJsonRecord077 : SourceJson :=
  (momentRecordsChunk077Push []).head (List.cons_ne_nil _ _)

theorem moment_record_077_push_eq (acc : List SourceJson) :
    momentRecordsChunk077Push acc = momentJsonRecord077 :: acc := by rfl

noncomputable def momentTypedRecord077 : MomentRecord :=
  { simplexId := 77,
    factorFloorsQ80 := #[(662169487438365402793 : Int), (679374085813435654438 : Int), (323943135638305597081 : Int), (598586686630360885964 : Int), (1270967977104195895342 : Int), (2364467735248376495552 : Int), (1937100647028269901520 : Int), (913157268642362052639 : Int), (802820781227082551546 : Int), (802843576697900375973 : Int)],
    oldFloorQ96 := (886455414668707 : Int),
    newFloorQ96 := (894081239025522 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_077_before_decode"
  err.flush

theorem decode_moment_record_077 :
    decodeMomentRecord momentJsonRecord077 = .ok momentTypedRecord077 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_077_decoded"
  err.flush

noncomputable def momentJsonRecord078 : SourceJson :=
  (momentRecordsChunk078Push []).head (List.cons_ne_nil _ _)

theorem moment_record_078_push_eq (acc : List SourceJson) :
    momentRecordsChunk078Push acc = momentJsonRecord078 :: acc := by rfl

noncomputable def momentTypedRecord078 : MomentRecord :=
  { simplexId := 78,
    factorFloorsQ80 := #[(601249166758601348628 : Int), (629986275131971548206 : Int), (309219568634267163674 : Int), (496405620030164404042 : Int), (1288427903248076661432 : Int), (2036661280764611627627 : Int), (1900565208536125935465 : Int), (897662490924819069369 : Int), (824461232593426012296 : Int), (820294949947608508613 : Int)],
    oldFloorQ96 := (9787794162011997730 : Int),
    newFloorQ96 := (9867500375553025675 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_078_before_decode"
  err.flush

theorem decode_moment_record_078 :
    decodeMomentRecord momentJsonRecord078 = .ok momentTypedRecord078 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_078_decoded"
  err.flush

noncomputable def momentJsonRecord079 : SourceJson :=
  (momentRecordsChunk079Push []).head (List.cons_ne_nil _ _)

theorem moment_record_079_push_eq (acc : List SourceJson) :
    momentRecordsChunk079Push acc = momentJsonRecord079 :: acc := by rfl

noncomputable def momentTypedRecord079 : MomentRecord :=
  { simplexId := 79,
    factorFloorsQ80 := #[(605541773956091072009 : Int), (622264426908476826823 : Int), (299360616156682196659 : Int), (505680611133809198124 : Int), (1244358722844209722706 : Int), (2037144438528606943069 : Int), (1841450992884537767855 : Int), (920980681580695100363 : Int), (901716544880079730857 : Int), (892513120519055278315 : Int)],
    oldFloorQ96 := (14460241092912809794 : Int),
    newFloorQ96 := (14578793884595846905 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_079_before_decode"
  err.flush

theorem decode_moment_record_079 :
    decodeMomentRecord momentJsonRecord079 = .ok momentTypedRecord079 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_079_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock019 : List SourceJson := [momentJsonRecord076, momentJsonRecord077, momentJsonRecord078, momentJsonRecord079]
noncomputable def momentTypedRecordsBlock019 : List MomentRecord := [momentTypedRecord076, momentTypedRecord077, momentTypedRecord078, momentTypedRecord079]

theorem moment_records_block_019_push_eq (acc : List SourceJson) :
    momentRecordsBlock019Push acc = [momentJsonRecord079, momentJsonRecord078, momentJsonRecord077, momentJsonRecord076] ++ acc := by rfl

theorem moment_records_block_019_reverse (acc : List SourceJson) :
    (momentRecordsBlock019Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock019 := by
  rw [moment_records_block_019_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_019 :
    momentJsonRecordsBlock019.mapM decodeMomentRecord = .ok momentTypedRecordsBlock019 := by
  simp only [momentJsonRecordsBlock019, momentTypedRecordsBlock019, List.mapM_cons, List.mapM_nil,
    decode_moment_record_076, decode_moment_record_077, decode_moment_record_078, decode_moment_record_079]
  rfl

noncomputable def momentTypedRowsThroughBlock019 : List MomentRecord := momentTypedRowsThroughBlock018 ++ momentTypedRecordsBlock019

theorem decode_moment_records_through_block_019 :
    momentRecordsAcc080.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock019 := by
  change (momentRecordsBlock019Push momentRecordsAcc076).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_019_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_018, decode_moment_records_block_019]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_019_complete"
  err.flush

#print axioms moment_record_076_push_eq
#print axioms decode_moment_record_076
#print axioms moment_record_077_push_eq
#print axioms decode_moment_record_077
#print axioms moment_record_078_push_eq
#print axioms decode_moment_record_078
#print axioms moment_record_079_push_eq
#print axioms decode_moment_record_079
#print axioms moment_records_block_019_push_eq
#print axioms moment_records_block_019_reverse
#print axioms decode_moment_records_block_019
#print axioms decode_moment_records_through_block_019

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
