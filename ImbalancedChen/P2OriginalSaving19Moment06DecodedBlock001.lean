/- SOURCE_CANDIDATE: original Cell06 source only. No Lean compilation,
independent kernel replay, full-owned audit or formal acceptance is claimed. -/

import ImbalancedChen.P2OriginalSaving19Moment06DecodedBlock000
import ImbalancedChen.P2OriginalSaving19Moment06RecordsBlock001

/-! Original typed moment records 4 through 7; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment06Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment06Parsing

noncomputable def momentJsonRecord004 : SourceJson :=
  (momentRecordsChunk004Push []).head (List.cons_ne_nil _ _)

theorem moment_record_004_push_eq (acc : List SourceJson) :
    momentRecordsChunk004Push acc = momentJsonRecord004 :: acc := by rfl

noncomputable def momentTypedRecord004 : MomentRecord :=
  { simplexId := 4,
    factorFloorsQ80 := #[(399746993640969932311 : Int), (322574017763977219789 : Int), (162541358449543498804 : Int), (260211956160100077827 : Int), (318160147023880163481 : Int), (188644963976537934025 : Int), (167177710085036645228 : Int), (165793683158724058089 : Int), (165804135259551178494 : Int), (341628698562233189691 : Int)],
    oldFloorQ96 := (1531849315719 : Int),
    newFloorQ96 := (1535010585831 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_004_before_decode"
  err.flush

theorem decode_moment_record_004 :
    decodeMomentRecord momentJsonRecord004 = .ok momentTypedRecord004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_004_decoded"
  err.flush

noncomputable def momentJsonRecord005 : SourceJson :=
  (momentRecordsChunk005Push []).head (List.cons_ne_nil _ _)

theorem moment_record_005_push_eq (acc : List SourceJson) :
    momentRecordsChunk005Push acc = momentJsonRecord005 :: acc := by rfl

noncomputable def momentTypedRecord005 : MomentRecord :=
  { simplexId := 5,
    factorFloorsQ80 := #[(394306864369286767142 : Int), (322707633537861781838 : Int), (149630181595989512613 : Int), (267417649773579482190 : Int), (314417894143113621271 : Int), (215773247939184097691 : Int), (827357021991167007100 : Int), (268960637689194021171 : Int), (268968727475439185052 : Int), (342928269760917556123 : Int)],
    oldFloorQ96 := (12094896839462 : Int),
    newFloorQ96 := (12128684356097 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_005_before_decode"
  err.flush

theorem decode_moment_record_005 :
    decodeMomentRecord momentJsonRecord005 = .ok momentTypedRecord005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_005_decoded"
  err.flush

noncomputable def momentJsonRecord006 : SourceJson :=
  (momentRecordsChunk006Push []).head (List.cons_ne_nil _ _)

theorem moment_record_006_push_eq (acc : List SourceJson) :
    momentRecordsChunk006Push acc = momentJsonRecord006 :: acc := by rfl

noncomputable def momentTypedRecord006 : MomentRecord :=
  { simplexId := 6,
    factorFloorsQ80 := #[(461260616459392116410 : Int), (418095021573093507849 : Int), (140039827998093327220 : Int), (253728267922598202131 : Int), (291699899289214806662 : Int), (251587526327103791613 : Int), (868816156784399042346 : Int), (405696208542681391422 : Int), (405708284899900747490 : Int), (509211930078050306237 : Int)],
    oldFloorQ96 := (59456828147417 : Int),
    newFloorQ96 := (59654168461887 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_006_before_decode"
  err.flush

theorem decode_moment_record_006 :
    decodeMomentRecord momentJsonRecord006 = .ok momentTypedRecord006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_006_decoded"
  err.flush

noncomputable def momentJsonRecord007 : SourceJson :=
  (momentRecordsChunk007Push []).head (List.cons_ne_nil _ _)

theorem moment_record_007_push_eq (acc : List SourceJson) :
    momentRecordsChunk007Push acc = momentJsonRecord007 :: acc := by rfl

noncomputable def momentTypedRecord007 : MomentRecord :=
  { simplexId := 7,
    factorFloorsQ80 := #[(321368809534411076357 : Int), (277384048590270028423 : Int), (174598554148722523189 : Int), (233795978185498388015 : Int), (302780383531803886825 : Int), (165202529551489917148 : Int), (150385400798557285251 : Int), (152219188195787069161 : Int), (202189479051263505110 : Int), (316703152640294174965 : Int)],
    oldFloorQ96 := (6691923872229998 : Int),
    newFloorQ96 := (6704648775492080 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_007_before_decode"
  err.flush

theorem decode_moment_record_007 :
    decodeMomentRecord momentJsonRecord007 = .ok momentTypedRecord007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_007_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock001 : List SourceJson := [momentJsonRecord004, momentJsonRecord005, momentJsonRecord006, momentJsonRecord007]
noncomputable def momentTypedRecordsBlock001 : List MomentRecord := [momentTypedRecord004, momentTypedRecord005, momentTypedRecord006, momentTypedRecord007]

theorem moment_records_block_001_push_eq (acc : List SourceJson) :
    momentRecordsBlock001Push acc = [momentJsonRecord007, momentJsonRecord006, momentJsonRecord005, momentJsonRecord004] ++ acc := by rfl

theorem moment_records_block_001_reverse (acc : List SourceJson) :
    (momentRecordsBlock001Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock001 := by
  rw [moment_records_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_001 :
    momentJsonRecordsBlock001.mapM decodeMomentRecord = .ok momentTypedRecordsBlock001 := by
  simp only [momentJsonRecordsBlock001, momentTypedRecordsBlock001, List.mapM_cons, List.mapM_nil,
    decode_moment_record_004, decode_moment_record_005, decode_moment_record_006, decode_moment_record_007]
  rfl

noncomputable def momentTypedRowsThroughBlock001 : List MomentRecord := momentTypedRowsThroughBlock000 ++ momentTypedRecordsBlock001

theorem decode_moment_records_through_block_001 :
    momentRecordsAcc008.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock001 := by
  change (momentRecordsBlock001Push momentRecordsAcc004).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_001_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_000, decode_moment_records_block_001]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_block_001_complete"
  err.flush

#print axioms moment_record_004_push_eq
#print axioms decode_moment_record_004
#print axioms moment_record_005_push_eq
#print axioms decode_moment_record_005
#print axioms moment_record_006_push_eq
#print axioms decode_moment_record_006
#print axioms moment_record_007_push_eq
#print axioms decode_moment_record_007
#print axioms moment_records_block_001_push_eq
#print axioms moment_records_block_001_reverse
#print axioms decode_moment_records_block_001
#print axioms decode_moment_records_through_block_001

end ImbalancedChen.P2OriginalSaving19Moment06Decoding
