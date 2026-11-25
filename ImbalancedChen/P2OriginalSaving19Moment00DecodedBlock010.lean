import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock009
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock010

/-! Original typed moment records 40 through 43; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord040 : SourceJson :=
  (momentRecordsChunk040Push []).head (List.cons_ne_nil _ _)

theorem moment_record_040_push_eq (acc : List SourceJson) :
    momentRecordsChunk040Push acc = momentJsonRecord040 :: acc := by rfl

noncomputable def momentTypedRecord040 : MomentRecord :=
  { simplexId := 40,
    factorFloorsQ80 := #[(359386790203265775796 : Int), (436965846873698896492 : Int), (160322990055090657241 : Int), (301379205867506824012 : Int), (298834069137849284614 : Int), (341714299981790945597 : Int), (307167501893042679294 : Int), (398851970471411786118 : Int), (316459688451786862985 : Int), (316488648952766087301 : Int)],
    oldFloorQ96 := (2756893735654 : Int),
    newFloorQ96 := (2764286746413 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_040_before_decode"
  err.flush

theorem decode_moment_record_040 :
    decodeMomentRecord momentJsonRecord040 = .ok momentTypedRecord040 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_040_decoded"
  err.flush

noncomputable def momentJsonRecord041 : SourceJson :=
  (momentRecordsChunk041Push []).head (List.cons_ne_nil _ _)

theorem moment_record_041_push_eq (acc : List SourceJson) :
    momentRecordsChunk041Push acc = momentJsonRecord041 :: acc := by rfl

noncomputable def momentTypedRecord041 : MomentRecord :=
  { simplexId := 41,
    factorFloorsQ80 := #[(198109967698141595236 : Int), (290856690436510339657 : Int), (106426201195992490154 : Int), (115156836861174526723 : Int), (200282464897374914120 : Int), (135234486421348114138 : Int), (309815744235959829647 : Int), (350569402798828043548 : Int), (213916790352901398492 : Int), (213937890752869837435 : Int)],
    oldFloorQ96 := (2342923990139 : Int),
    newFloorQ96 := (2347063974959 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_041_before_decode"
  err.flush

theorem decode_moment_record_041 :
    decodeMomentRecord momentJsonRecord041 = .ok momentTypedRecord041 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_041_decoded"
  err.flush

noncomputable def momentJsonRecord042 : SourceJson :=
  (momentRecordsChunk042Push []).head (List.cons_ne_nil _ _)

theorem moment_record_042_push_eq (acc : List SourceJson) :
    momentRecordsChunk042Push acc = momentJsonRecord042 :: acc := by rfl

noncomputable def momentTypedRecord042 : MomentRecord :=
  { simplexId := 42,
    factorFloorsQ80 := #[(179496507450653797042 : Int), (184196271079966226343 : Int), (151429234644055812713 : Int), (428161754319302351542 : Int), (189824703602836185560 : Int), (386511930819990640209 : Int), (502668042231772069266 : Int), (331124921425285913032 : Int), (340663253254247464065 : Int), (306758819525347775234 : Int)],
    oldFloorQ96 := (8516914870344 : Int),
    newFloorQ96 := (8538082096719 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_042_before_decode"
  err.flush

theorem decode_moment_record_042 :
    decodeMomentRecord momentJsonRecord042 = .ok momentTypedRecord042 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_042_decoded"
  err.flush

noncomputable def momentJsonRecord043 : SourceJson :=
  (momentRecordsChunk043Push []).head (List.cons_ne_nil _ _)

theorem moment_record_043_push_eq (acc : List SourceJson) :
    momentRecordsChunk043Push acc = momentJsonRecord043 :: acc := by rfl

noncomputable def momentTypedRecord043 : MomentRecord :=
  { simplexId := 43,
    factorFloorsQ80 := #[(157466646558345457389 : Int), (163170555652092043720 : Int), (145813554009327071173 : Int), (387424656555296371215 : Int), (192290825987015310828 : Int), (354471944618354418853 : Int), (491838342711108480480 : Int), (326858059602397788836 : Int), (344957571067631858319 : Int), (306521488854628640806 : Int)],
    oldFloorQ96 := (71166403669235882 : Int),
    newFloorQ96 := (71335602020098361 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_043_before_decode"
  err.flush

theorem decode_moment_record_043 :
    decodeMomentRecord momentJsonRecord043 = .ok momentTypedRecord043 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_043_decoded"
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
  err.putStrLn "P26_MOMENT00 typed_block_010_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
