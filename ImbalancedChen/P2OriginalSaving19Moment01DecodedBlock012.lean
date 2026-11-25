import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock011
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock012

/-! Original typed moment records 48 through 51; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord048 : SourceJson :=
  (momentRecordsChunk048Push []).head (List.cons_ne_nil _ _)

theorem moment_record_048_push_eq (acc : List SourceJson) :
    momentRecordsChunk048Push acc = momentJsonRecord048 :: acc := by rfl

noncomputable def momentTypedRecord048 : MomentRecord :=
  { simplexId := 48,
    factorFloorsQ80 := #[(2290737815154384620108 : Int), (2494647271190127158834 : Int), (249433616674851358006 : Int), (599651159297671215676 : Int), (1139152180938862130564 : Int), (1617594802519474237076 : Int), (1463383960461067853225 : Int), (1247016013731836415486 : Int), (1082063673710529470612 : Int), (1719585064415090618748 : Int)],
    oldFloorQ96 := (165942871511582641 : Int),
    newFloorQ96 := (167862315468005478 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_048_before_decode"
  err.flush

theorem decode_moment_record_048 :
    decodeMomentRecord momentJsonRecord048 = .ok momentTypedRecord048 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_048_decoded"
  err.flush

noncomputable def momentJsonRecord049 : SourceJson :=
  (momentRecordsChunk049Push []).head (List.cons_ne_nil _ _)

theorem moment_record_049_push_eq (acc : List SourceJson) :
    momentRecordsChunk049Push acc = momentJsonRecord049 :: acc := by rfl

noncomputable def momentTypedRecord049 : MomentRecord :=
  { simplexId := 49,
    factorFloorsQ80 := #[(2106887019086810958051 : Int), (2068807924336936831208 : Int), (193533250678347078130 : Int), (615446042086396737405 : Int), (1169735229884601520912 : Int), (1615027099723655440102 : Int), (1216820712513592918567 : Int), (1075302495066071023229 : Int), (973841915807523961428 : Int), (1339047940304520182507 : Int)],
    oldFloorQ96 := (5162182915136402 : Int),
    newFloorQ96 := (5215293881468097 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_049_before_decode"
  err.flush

theorem decode_moment_record_049 :
    decodeMomentRecord momentJsonRecord049 = .ok momentTypedRecord049 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_049_decoded"
  err.flush

noncomputable def momentJsonRecord050 : SourceJson :=
  (momentRecordsChunk050Push []).head (List.cons_ne_nil _ _)

theorem moment_record_050_push_eq (acc : List SourceJson) :
    momentRecordsChunk050Push acc = momentJsonRecord050 :: acc := by rfl

noncomputable def momentTypedRecord050 : MomentRecord :=
  { simplexId := 50,
    factorFloorsQ80 := #[(1928137393708241637046 : Int), (1898907399991988276691 : Int), (178545347534146149974 : Int), (654091294015889473715 : Int), (1216978200245136276869 : Int), (1631014342793043636998 : Int), (1182887699726949443144 : Int), (1064958237352344337978 : Int), (983394769811411997631 : Int), (920256541153793329788 : Int)],
    oldFloorQ96 := (1732242175876476 : Int),
    newFloorQ96 := (1749029153934780 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_050_before_decode"
  err.flush

theorem decode_moment_record_050 :
    decodeMomentRecord momentJsonRecord050 = .ok momentTypedRecord050 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_050_decoded"
  err.flush

noncomputable def momentJsonRecord051 : SourceJson :=
  (momentRecordsChunk051Push []).head (List.cons_ne_nil _ _)

theorem moment_record_051_push_eq (acc : List SourceJson) :
    momentRecordsChunk051Push acc = momentJsonRecord051 :: acc := by rfl

noncomputable def momentTypedRecord051 : MomentRecord :=
  { simplexId := 51,
    factorFloorsQ80 := #[(2118003908745442505155 : Int), (2291351696110744171988 : Int), (256915802021773521761 : Int), (549847027638373832056 : Int), (1025524530442785119358 : Int), (1716652034033562847037 : Int), (1347172700443926769650 : Int), (1102384615561808277418 : Int), (991572934957718527120 : Int), (1986505079762934346653 : Int)],
    oldFloorQ96 := (1401072330848752047 : Int),
    newFloorQ96 := (1416672023373585356 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_051_before_decode"
  err.flush

theorem decode_moment_record_051 :
    decodeMomentRecord momentJsonRecord051 = .ok momentTypedRecord051 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_051_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock012 : List SourceJson := [momentJsonRecord048, momentJsonRecord049, momentJsonRecord050, momentJsonRecord051]
noncomputable def momentTypedRecordsBlock012 : List MomentRecord := [momentTypedRecord048, momentTypedRecord049, momentTypedRecord050, momentTypedRecord051]

theorem moment_records_block_012_push_eq (acc : List SourceJson) :
    momentRecordsBlock012Push acc = [momentJsonRecord051, momentJsonRecord050, momentJsonRecord049, momentJsonRecord048] ++ acc := by rfl

theorem moment_records_block_012_reverse (acc : List SourceJson) :
    (momentRecordsBlock012Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock012 := by
  rw [moment_records_block_012_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_012 :
    momentJsonRecordsBlock012.mapM decodeMomentRecord = .ok momentTypedRecordsBlock012 := by
  simp only [momentJsonRecordsBlock012, momentTypedRecordsBlock012, List.mapM_cons, List.mapM_nil,
    decode_moment_record_048, decode_moment_record_049, decode_moment_record_050, decode_moment_record_051]
  rfl

noncomputable def momentTypedRowsThroughBlock012 : List MomentRecord := momentTypedRowsThroughBlock011 ++ momentTypedRecordsBlock012

theorem decode_moment_records_through_block_012 :
    momentRecordsAcc052.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock012 := by
  change (momentRecordsBlock012Push momentRecordsAcc048).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_012_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_011, decode_moment_records_block_012]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_012_complete"
  err.flush

#print axioms moment_record_048_push_eq
#print axioms decode_moment_record_048
#print axioms moment_record_049_push_eq
#print axioms decode_moment_record_049
#print axioms moment_record_050_push_eq
#print axioms decode_moment_record_050
#print axioms moment_record_051_push_eq
#print axioms decode_moment_record_051
#print axioms moment_records_block_012_push_eq
#print axioms moment_records_block_012_reverse
#print axioms decode_moment_records_block_012
#print axioms decode_moment_records_through_block_012

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
