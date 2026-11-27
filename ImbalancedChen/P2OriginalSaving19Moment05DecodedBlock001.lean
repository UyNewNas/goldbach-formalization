import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock000
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock001

/-! Original typed moment records 4 through 7; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord004 : SourceJson :=
  (momentRecordsChunk004Push []).head (List.cons_ne_nil _ _)

theorem moment_record_004_push_eq (acc : List SourceJson) :
    momentRecordsChunk004Push acc = momentJsonRecord004 :: acc := by rfl

noncomputable def momentTypedRecord004 : MomentRecord :=
  { simplexId := 4,
    factorFloorsQ80 := #[(163030686478804900449 : Int), (176376627343813538111 : Int), (77900661484784343570 : Int), (321983820578711766150 : Int), (172830427384198978491 : Int), (179429508195080156876 : Int), (564447283654827798278 : Int), (523518933330542982321 : Int), (574175040596758037345 : Int), (536339113047512631664 : Int)],
    oldFloorQ96 := (2490951933565 : Int),
    newFloorQ96 := (2497740169351 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_004_before_decode"
  err.flush

theorem decode_moment_record_004 :
    decodeMomentRecord momentJsonRecord004 = .ok momentTypedRecord004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_004_decoded"
  err.flush

noncomputable def momentJsonRecord005 : SourceJson :=
  (momentRecordsChunk005Push []).head (List.cons_ne_nil _ _)

theorem moment_record_005_push_eq (acc : List SourceJson) :
    momentRecordsChunk005Push acc = momentJsonRecord005 :: acc := by rfl

noncomputable def momentTypedRecord005 : MomentRecord :=
  { simplexId := 5,
    factorFloorsQ80 := #[(152336804504261418231 : Int), (161590784207813795919 : Int), (77900661484784343570 : Int), (275342438915167193370 : Int), (172830427384198978491 : Int), (179429508195080156876 : Int), (564447283654827798278 : Int), (523518933330542982321 : Int), (477697567408958927381 : Int), (369830084101985024239 : Int)],
    oldFloorQ96 := (26010400021829131 : Int),
    newFloorQ96 := (26074053866131647 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_005_before_decode"
  err.flush

theorem decode_moment_record_005 :
    decodeMomentRecord momentJsonRecord005 = .ok momentTypedRecord005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_005_decoded"
  err.flush

noncomputable def momentJsonRecord006 : SourceJson :=
  (momentRecordsChunk006Push []).head (List.cons_ne_nil _ _)

theorem moment_record_006_push_eq (acc : List SourceJson) :
    momentRecordsChunk006Push acc = momentJsonRecord006 :: acc := by rfl

noncomputable def momentTypedRecord006 : MomentRecord :=
  { simplexId := 6,
    factorFloorsQ80 := #[(139770699093274383720 : Int), (144130207421808531415 : Int), (78439962934712640083 : Int), (274770037623090484907 : Int), (186858589286485257000 : Int), (177201222546624626557 : Int), (570876984966238036327 : Int), (462656376707245122633 : Int), (324081819703087164939 : Int), (324116249968799175752 : Int)],
    oldFloorQ96 := (1912603018043 : Int),
    newFloorQ96 := (1916852265361 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_006_before_decode"
  err.flush

theorem decode_moment_record_006 :
    decodeMomentRecord momentJsonRecord006 = .ok momentTypedRecord006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_006_decoded"
  err.flush

noncomputable def momentJsonRecord007 : SourceJson :=
  (momentRecordsChunk007Push []).head (List.cons_ne_nil _ _)

theorem moment_record_007_push_eq (acc : List SourceJson) :
    momentRecordsChunk007Push acc = momentJsonRecord007 :: acc := by rfl

noncomputable def momentTypedRecord007 : MomentRecord :=
  { simplexId := 7,
    factorFloorsQ80 := #[(318229222374638685345 : Int), (341476877960280449767 : Int), (142739707360396578541 : Int), (374455781832487082964 : Int), (307343595193194539610 : Int), (328812138642788927124 : Int), (1091869406673231295252 : Int), (500682962688908690545 : Int), (498938640202592110928 : Int), (380216151439270235518 : Int)],
    oldFloorQ96 := (2405998178201 : Int),
    newFloorQ96 := (2414540825038 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_007_before_decode"
  err.flush

theorem decode_moment_record_007 :
    decodeMomentRecord momentJsonRecord007 = .ok momentTypedRecord007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_007_decoded"
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
  err.putStrLn "P26_MOMENT05 typed_block_001_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
