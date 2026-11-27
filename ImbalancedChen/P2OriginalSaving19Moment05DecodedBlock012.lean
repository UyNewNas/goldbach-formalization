import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock011
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock012

/-! Original typed moment records 48 through 51; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord048 : SourceJson :=
  (momentRecordsChunk048Push []).head (List.cons_ne_nil _ _)

theorem moment_record_048_push_eq (acc : List SourceJson) :
    momentRecordsChunk048Push acc = momentJsonRecord048 :: acc := by rfl

noncomputable def momentTypedRecord048 : MomentRecord :=
  { simplexId := 48,
    factorFloorsQ80 := #[(263458160292516850759 : Int), (329385111646603228851 : Int), (88173380080299264726 : Int), (117096089980037332631 : Int), (212865806263928698067 : Int), (144255522689224992128 : Int), (684137126061121878578 : Int), (287020222945689622195 : Int), (251017840199467442215 : Int), (251013557253471728868 : Int)],
    oldFloorQ96 := (907869497315 : Int),
    newFloorQ96 := (909845516710 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_048_before_decode"
  err.flush

theorem decode_moment_record_048 :
    decodeMomentRecord momentJsonRecord048 = .ok momentTypedRecord048 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_048_decoded"
  err.flush

noncomputable def momentJsonRecord049 : SourceJson :=
  (momentRecordsChunk049Push []).head (List.cons_ne_nil _ _)

theorem moment_record_049_push_eq (acc : List SourceJson) :
    momentRecordsChunk049Push acc = momentJsonRecord049 :: acc := by rfl

noncomputable def momentTypedRecord049 : MomentRecord :=
  { simplexId := 49,
    factorFloorsQ80 := #[(194200248045369545809 : Int), (205956719744326382548 : Int), (130346365846797553227 : Int), (428331550650980745027 : Int), (269140270722857220741 : Int), (291282842142967127154 : Int), (608055474684503941736 : Int), (621113024768354449963 : Int), (428668345799906116112 : Int), (428698756860801327289 : Int)],
    oldFloorQ96 := (2009596185705 : Int),
    newFloorQ96 := (2015599040542 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_049_before_decode"
  err.flush

theorem decode_moment_record_049 :
    decodeMomentRecord momentJsonRecord049 = .ok momentTypedRecord049 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_049_decoded"
  err.flush

noncomputable def momentJsonRecord050 : SourceJson :=
  (momentRecordsChunk050Push []).head (List.cons_ne_nil _ _)

theorem moment_record_050_push_eq (acc : List SourceJson) :
    momentRecordsChunk050Push acc = momentJsonRecord050 :: acc := by rfl

noncomputable def momentTypedRecord050 : MomentRecord :=
  { simplexId := 50,
    factorFloorsQ80 := #[(359291005799095925929 : Int), (383354217188018568538 : Int), (171572738067385210430 : Int), (482190447098243103123 : Int), (365673826829468983346 : Int), (387192164672560668939 : Int), (769401602403209598422 : Int), (623998493668305183916 : Int), (428685801691020311777 : Int), (428716103024226706983 : Int)],
    oldFloorQ96 := (1903848708063 : Int),
    newFloorQ96 := (1910790691584 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_050_before_decode"
  err.flush

theorem decode_moment_record_050 :
    decodeMomentRecord momentJsonRecord050 = .ok momentTypedRecord050 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_050_decoded"
  err.flush

noncomputable def momentJsonRecord051 : SourceJson :=
  (momentRecordsChunk051Push []).head (List.cons_ne_nil _ _)

theorem moment_record_051_push_eq (acc : List SourceJson) :
    momentRecordsChunk051Push acc = momentJsonRecord051 :: acc := by rfl

noncomputable def momentTypedRecord051 : MomentRecord :=
  { simplexId := 51,
    factorFloorsQ80 := #[(399697014089122227221 : Int), (427305278993350210561 : Int), (186984904912657733888 : Int), (447031126837876829515 : Int), (380153197293999328105 : Int), (419379954055764622975 : Int), (893773737155940780918 : Int), (492096007530751513906 : Int), (259222920386702374237 : Int), (259246230577880291235 : Int)],
    oldFloorQ96 := (1345204430482 : Int),
    newFloorQ96 := (1349846808722 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_051_before_decode"
  err.flush

theorem decode_moment_record_051 :
    decodeMomentRecord momentJsonRecord051 = .ok momentTypedRecord051 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_051_decoded"
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
  err.putStrLn "P26_MOMENT05 typed_block_012_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
