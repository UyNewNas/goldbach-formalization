import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock033
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock034

/-! Original typed moment records 136 through 139; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord136 : SourceJson :=
  (momentRecordsChunk136Push []).head (List.cons_ne_nil _ _)

theorem moment_record_136_push_eq (acc : List SourceJson) :
    momentRecordsChunk136Push acc = momentJsonRecord136 :: acc := by rfl

noncomputable def momentTypedRecord136 : MomentRecord :=
  { simplexId := 136,
    factorFloorsQ80 := #[(1040627983815738901493 : Int), (1021225163663359976401 : Int), (162577756692648409207 : Int), (927562737124208842201 : Int), (522250620667513449875 : Int), (1755321617160991688034 : Int), (1482897236775135496006 : Int), (1373221883427890936343 : Int), (1275079948339746143127 : Int), (1275138266621724068577 : Int)],
    oldFloorQ96 := (44126752063 : Int),
    newFloorQ96 := (44524048995 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_136_before_decode"
  err.flush

theorem decode_moment_record_136 :
    decodeMomentRecord momentJsonRecord136 = .ok momentTypedRecord136 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_136_decoded"
  err.flush

noncomputable def momentJsonRecord137 : SourceJson :=
  (momentRecordsChunk137Push []).head (List.cons_ne_nil _ _)

theorem moment_record_137_push_eq (acc : List SourceJson) :
    momentRecordsChunk137Push acc = momentJsonRecord137 :: acc := by rfl

noncomputable def momentTypedRecord137 : MomentRecord :=
  { simplexId := 137,
    factorFloorsQ80 := #[(672340127396285992698 : Int), (660172965567475885040 : Int), (108411906412357963216 : Int), (543407106198183644719 : Int), (446832977862209237334 : Int), (1021231706523182077269 : Int), (787173847929004390792 : Int), (710910625236126536415 : Int), (685288135703069409143 : Int), (746647451171948552868 : Int)],
    oldFloorQ96 := (1041751810873593 : Int),
    newFloorQ96 := (1047266190841402 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_137_before_decode"
  err.flush

theorem decode_moment_record_137 :
    decodeMomentRecord momentJsonRecord137 = .ok momentTypedRecord137 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_137_decoded"
  err.flush

noncomputable def momentJsonRecord138 : SourceJson :=
  (momentRecordsChunk138Push []).head (List.cons_ne_nil _ _)

theorem moment_record_138_push_eq (acc : List SourceJson) :
    momentRecordsChunk138Push acc = momentJsonRecord138 :: acc := by rfl

noncomputable def momentTypedRecord138 : MomentRecord :=
  { simplexId := 138,
    factorFloorsQ80 := #[(678212121932886882171 : Int), (668126458688862455517 : Int), (103578796873875198919 : Int), (587978450877196654181 : Int), (464919323093132494712 : Int), (1003667315285838178973 : Int), (800674291118395137314 : Int), (733660612798315630973 : Int), (681929675337172650171 : Int), (681978045989526373309 : Int)],
    oldFloorQ96 := (40838155597 : Int),
    newFloorQ96 := (41055084730 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_138_before_decode"
  err.flush

theorem decode_moment_record_138 :
    decodeMomentRecord momentJsonRecord138 = .ok momentTypedRecord138 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_138_decoded"
  err.flush

noncomputable def momentJsonRecord139 : SourceJson :=
  (momentRecordsChunk139Push []).head (List.cons_ne_nil _ _)

theorem moment_record_139_push_eq (acc : List SourceJson) :
    momentRecordsChunk139Push acc = momentJsonRecord139 :: acc := by rfl

noncomputable def momentTypedRecord139 : MomentRecord :=
  { simplexId := 139,
    factorFloorsQ80 := #[(683299456367513418802 : Int), (669309448433493033494 : Int), (103006284683235126209 : Int), (566369292894266042393 : Int), (462307528953224318987 : Int), (967730455913858092844 : Int), (800062958165941408320 : Int), (732591006789941212351 : Int), (683909925012446289007 : Int), (674616034387096981852 : Int)],
    oldFloorQ96 := (97961452662423 : Int),
    newFloorQ96 := (98476804695393 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_139_before_decode"
  err.flush

theorem decode_moment_record_139 :
    decodeMomentRecord momentJsonRecord139 = .ok momentTypedRecord139 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_139_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock034 : List SourceJson := [momentJsonRecord136, momentJsonRecord137, momentJsonRecord138, momentJsonRecord139]
noncomputable def momentTypedRecordsBlock034 : List MomentRecord := [momentTypedRecord136, momentTypedRecord137, momentTypedRecord138, momentTypedRecord139]

theorem moment_records_block_034_push_eq (acc : List SourceJson) :
    momentRecordsBlock034Push acc = [momentJsonRecord139, momentJsonRecord138, momentJsonRecord137, momentJsonRecord136] ++ acc := by rfl

theorem moment_records_block_034_reverse (acc : List SourceJson) :
    (momentRecordsBlock034Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock034 := by
  rw [moment_records_block_034_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_034 :
    momentJsonRecordsBlock034.mapM decodeMomentRecord = .ok momentTypedRecordsBlock034 := by
  simp only [momentJsonRecordsBlock034, momentTypedRecordsBlock034, List.mapM_cons, List.mapM_nil,
    decode_moment_record_136, decode_moment_record_137, decode_moment_record_138, decode_moment_record_139]
  rfl

noncomputable def momentTypedRowsThroughBlock034 : List MomentRecord := momentTypedRowsThroughBlock033 ++ momentTypedRecordsBlock034

theorem decode_moment_records_through_block_034 :
    momentRecordsAcc140.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock034 := by
  change (momentRecordsBlock034Push momentRecordsAcc136).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_034_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_033, decode_moment_records_block_034]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_034_complete"
  err.flush

#print axioms moment_record_136_push_eq
#print axioms decode_moment_record_136
#print axioms moment_record_137_push_eq
#print axioms decode_moment_record_137
#print axioms moment_record_138_push_eq
#print axioms decode_moment_record_138
#print axioms moment_record_139_push_eq
#print axioms decode_moment_record_139
#print axioms moment_records_block_034_push_eq
#print axioms moment_records_block_034_reverse
#print axioms decode_moment_records_block_034
#print axioms decode_moment_records_through_block_034

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
