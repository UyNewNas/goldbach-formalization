import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock011
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock012

/-! Original typed moment records 48 through 51; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord048 : SourceJson :=
  (momentRecordsChunk048Push []).head (List.cons_ne_nil _ _)

theorem moment_record_048_push_eq (acc : List SourceJson) :
    momentRecordsChunk048Push acc = momentJsonRecord048 :: acc := by rfl

noncomputable def momentTypedRecord048 : MomentRecord :=
  { simplexId := 48,
    factorFloorsQ80 := #[(145499004485738626575 : Int), (144940066948542972020 : Int), (152401866257385263563 : Int), (395310186532257928353 : Int), (276552899496665477469 : Int), (365107896738262497996 : Int), (502660587941122851681 : Int), (331120242969629628582 : Int), (247617780989145653154 : Int), (247641256192517854207 : Int)],
    oldFloorQ96 := (6447953083374 : Int),
    newFloorQ96 := (6462951853978 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_048_before_decode"
  err.flush

theorem decode_moment_record_048 :
    decodeMomentRecord momentJsonRecord048 = .ok momentTypedRecord048 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_048_decoded"
  err.flush

noncomputable def momentJsonRecord049 : SourceJson :=
  (momentRecordsChunk049Push []).head (List.cons_ne_nil _ _)

theorem moment_record_049_push_eq (acc : List SourceJson) :
    momentRecordsChunk049Push acc = momentJsonRecord049 :: acc := by rfl

noncomputable def momentTypedRecord049 : MomentRecord :=
  { simplexId := 49,
    factorFloorsQ80 := #[(189249753509695974985 : Int), (217065192721833738602 : Int), (239071124466418803741 : Int), (652804722855930336999 : Int), (238219668652768164554 : Int), (593127755752091767521 : Int), (674969110648204718664 : Int), (668407718279238085059 : Int), (426411566123614454824 : Int), (426434093511673412525 : Int)],
    oldFloorQ96 := (5359109671120 : Int),
    newFloorQ96 := (5378319907414 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_049_before_decode"
  err.flush

theorem decode_moment_record_049 :
    decodeMomentRecord momentJsonRecord049 = .ok momentTypedRecord049 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_049_decoded"
  err.flush

noncomputable def momentJsonRecord050 : SourceJson :=
  (momentRecordsChunk050Push []).head (List.cons_ne_nil _ _)

theorem moment_record_050_push_eq (acc : List SourceJson) :
    momentRecordsChunk050Push acc = momentJsonRecord050 :: acc := by rfl

noncomputable def momentTypedRecord050 : MomentRecord :=
  { simplexId := 50,
    factorFloorsQ80 := #[(357323081668075344710 : Int), (403718595370892469596 : Int), (251678985465814565054 : Int), (647275065724156455207 : Int), (333275316008921282571 : Int), (616071838214495632950 : Int), (489232720663936030483 : Int), (671968333697495250082 : Int), (426680767712134181414 : Int), (426703179443039705286 : Int)],
    oldFloorQ96 := (5100195194032 : Int),
    newFloorQ96 := (5119739894104 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_050_before_decode"
  err.flush

theorem decode_moment_record_050 :
    decodeMomentRecord momentJsonRecord050 = .ok momentTypedRecord050 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_050_decoded"
  err.flush

noncomputable def momentJsonRecord051 : SourceJson :=
  (momentRecordsChunk051Push []).head (List.cons_ne_nil _ _)

theorem moment_record_051_push_eq (acc : List SourceJson) :
    momentRecordsChunk051Push acc = momentJsonRecord051 :: acc := by rfl

noncomputable def momentTypedRecord051 : MomentRecord :=
  { simplexId := 51,
    factorFloorsQ80 := #[(398580933963451437897 : Int), (450322804449477123253 : Int), (239741712200384594155 : Int), (509311805717154312223 : Int), (346803706771043326519 : Int), (562447685810413478509 : Int), (423844617290502588476 : Int), (563477369112442196448 : Int), (273002351132706585391 : Int), (273017406668147155334 : Int)],
    oldFloorQ96 := (3615346740085 : Int),
    newFloorQ96 := (3627450402311 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_051_before_decode"
  err.flush

theorem decode_moment_record_051 :
    decodeMomentRecord momentJsonRecord051 = .ok momentTypedRecord051 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_051_decoded"
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
  err.putStrLn "P26_MOMENT00 typed_block_012_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
