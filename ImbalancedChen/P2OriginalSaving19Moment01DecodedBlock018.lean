import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock017
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock018

/-! Original typed moment records 72 through 75; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord072 : SourceJson :=
  (momentRecordsChunk072Push []).head (List.cons_ne_nil _ _)

theorem moment_record_072_push_eq (acc : List SourceJson) :
    momentRecordsChunk072Push acc = momentJsonRecord072 :: acc := by rfl

noncomputable def momentTypedRecord072 : MomentRecord :=
  { simplexId := 72,
    factorFloorsQ80 := #[(1066810848600362022201 : Int), (1062884549766058567256 : Int), (118635164974403257804 : Int), (645333705149971276424 : Int), (1259482706912829410749 : Int), (1178230301789968329257 : Int), (902698140076520485222 : Int), (814538151486630934945 : Int), (739877981015015433649 : Int), (739944835376781072287 : Int)],
    oldFloorQ96 := (35974035084 : Int),
    newFloorQ96 := (36228713234 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_072_before_decode"
  err.flush

theorem decode_moment_record_072 :
    decodeMomentRecord momentJsonRecord072 = .ok momentTypedRecord072 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_072_decoded"
  err.flush

noncomputable def momentJsonRecord073 : SourceJson :=
  (momentRecordsChunk073Push []).head (List.cons_ne_nil _ _)

theorem moment_record_073_push_eq (acc : List SourceJson) :
    momentRecordsChunk073Push acc = momentJsonRecord073 :: acc := by rfl

noncomputable def momentTypedRecord073 : MomentRecord :=
  { simplexId := 73,
    factorFloorsQ80 := #[(1065335703936183843223 : Int), (1061599459879016932770 : Int), (117973648068139789488 : Int), (619010452711833438680 : Int), (1249922645705564636434 : Int), (1133469407811906088341 : Int), (901582335131404848157 : Int), (812928778163222583896 : Int), (742692423776044179860 : Int), (728748991125978768212 : Int)],
    oldFloorQ96 := (86321809714820 : Int),
    newFloorQ96 := (86926081377880 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_073_before_decode"
  err.flush

theorem decode_moment_record_073 :
    decodeMomentRecord momentJsonRecord073 = .ok momentTypedRecord073 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_073_decoded"
  err.flush

noncomputable def momentJsonRecord074 : SourceJson :=
  (momentRecordsChunk074Push []).head (List.cons_ne_nil _ _)

theorem moment_record_074_push_eq (acc : List SourceJson) :
    momentRecordsChunk074Push acc = momentJsonRecord074 :: acc := by rfl

noncomputable def momentTypedRecord074 : MomentRecord :=
  { simplexId := 74,
    factorFloorsQ80 := #[(1065426639446222839427 : Int), (1062469511822407317442 : Int), (119115488884079841410 : Int), (614526619548414520221 : Int), (1237483785938460124595 : Int), (1133906249861084793551 : Int), (896523756380932317327 : Int), (805737971236641799389 : Int), (747010357329940439529 : Int), (706841268912335434153 : Int)],
    oldFloorQ96 := (218557906067138 : Int),
    newFloorQ96 := (220079808893274 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_074_before_decode"
  err.flush

theorem decode_moment_record_074 :
    decodeMomentRecord momentJsonRecord074 = .ok momentTypedRecord074 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_074_decoded"
  err.flush

noncomputable def momentJsonRecord075 : SourceJson :=
  (momentRecordsChunk075Push []).head (List.cons_ne_nil _ _)

theorem moment_record_075_push_eq (acc : List SourceJson) :
    momentRecordsChunk075Push acc = momentJsonRecord075 :: acc := by rfl

noncomputable def momentTypedRecord075 : MomentRecord :=
  { simplexId := 75,
    factorFloorsQ80 := #[(1077647129801634009353 : Int), (1072468023366200576492 : Int), (124334018995623896297 : Int), (587900307936500729078 : Int), (1202923866291782261758 : Int), (1198976712768577296384 : Int), (940267292176213135372 : Int), (744281779667074188965 : Int), (744277170264575525443 : Int), (759580979272999250091 : Int)],
    oldFloorQ96 := (229294168755 : Int),
    newFloorQ96 := (230902982479 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_075_before_decode"
  err.flush

theorem decode_moment_record_075 :
    decodeMomentRecord momentJsonRecord075 = .ok momentTypedRecord075 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_075_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock018 : List SourceJson := [momentJsonRecord072, momentJsonRecord073, momentJsonRecord074, momentJsonRecord075]
noncomputable def momentTypedRecordsBlock018 : List MomentRecord := [momentTypedRecord072, momentTypedRecord073, momentTypedRecord074, momentTypedRecord075]

theorem moment_records_block_018_push_eq (acc : List SourceJson) :
    momentRecordsBlock018Push acc = [momentJsonRecord075, momentJsonRecord074, momentJsonRecord073, momentJsonRecord072] ++ acc := by rfl

theorem moment_records_block_018_reverse (acc : List SourceJson) :
    (momentRecordsBlock018Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock018 := by
  rw [moment_records_block_018_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_018 :
    momentJsonRecordsBlock018.mapM decodeMomentRecord = .ok momentTypedRecordsBlock018 := by
  simp only [momentJsonRecordsBlock018, momentTypedRecordsBlock018, List.mapM_cons, List.mapM_nil,
    decode_moment_record_072, decode_moment_record_073, decode_moment_record_074, decode_moment_record_075]
  rfl

noncomputable def momentTypedRowsThroughBlock018 : List MomentRecord := momentTypedRowsThroughBlock017 ++ momentTypedRecordsBlock018

theorem decode_moment_records_through_block_018 :
    momentRecordsAcc076.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock018 := by
  change (momentRecordsBlock018Push momentRecordsAcc072).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_018_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_017, decode_moment_records_block_018]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_018_complete"
  err.flush

#print axioms moment_record_072_push_eq
#print axioms decode_moment_record_072
#print axioms moment_record_073_push_eq
#print axioms decode_moment_record_073
#print axioms moment_record_074_push_eq
#print axioms decode_moment_record_074
#print axioms moment_record_075_push_eq
#print axioms decode_moment_record_075
#print axioms moment_records_block_018_push_eq
#print axioms moment_records_block_018_reverse
#print axioms decode_moment_records_block_018
#print axioms decode_moment_records_through_block_018

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
