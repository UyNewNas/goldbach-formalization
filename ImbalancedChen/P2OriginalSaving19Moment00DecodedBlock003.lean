import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock002
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock003

/-! Original typed moment records 12 through 15; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord012 : SourceJson :=
  (momentRecordsChunk012Push []).head (List.cons_ne_nil _ _)

theorem moment_record_012_push_eq (acc : List SourceJson) :
    momentRecordsChunk012Push acc = momentJsonRecord012 :: acc := by rfl

noncomputable def momentTypedRecord012 : MomentRecord :=
  { simplexId := 12,
    factorFloorsQ80 := #[(379910269297712058788 : Int), (447630788771353052947 : Int), (203852244741706390431 : Int), (395723257189789813825 : Int), (361766906480056624651 : Int), (420413956247063237197 : Int), (292266257964670050679 : Int), (467049434654594674265 : Int), (542908266613918828823 : Int), (266266483852827150975 : Int)],
    oldFloorQ96 := (37681737894353939 : Int),
    newFloorQ96 := (37799674216721593 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_012_before_decode"
  err.flush

theorem decode_moment_record_012 :
    decodeMomentRecord momentJsonRecord012 = .ok momentTypedRecord012 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_012_decoded"
  err.flush

noncomputable def momentJsonRecord013 : SourceJson :=
  (momentRecordsChunk013Push []).head (List.cons_ne_nil _ _)

theorem moment_record_013_push_eq (acc : List SourceJson) :
    momentRecordsChunk013Push acc = momentJsonRecord013 :: acc := by rfl

noncomputable def momentTypedRecord013 : MomentRecord :=
  { simplexId := 13,
    factorFloorsQ80 := #[(372983411282180109264 : Int), (415240618381173659928 : Int), (202988292352503714263 : Int), (435525985995954342413 : Int), (372057105376070398571 : Int), (433823421228557579686 : Int), (308470983376377608335 : Int), (493446980073299762750 : Int), (621060236185297637616 : Int), (245858025033950465503 : Int)],
    oldFloorQ96 := (42627328010212917 : Int),
    newFloorQ96 := (42765117481440471 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_013_before_decode"
  err.flush

theorem decode_moment_record_013 :
    decodeMomentRecord momentJsonRecord013 = .ok momentTypedRecord013 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_013_decoded"
  err.flush

noncomputable def momentJsonRecord014 : SourceJson :=
  (momentRecordsChunk014Push []).head (List.cons_ne_nil _ _)

theorem moment_record_014_push_eq (acc : List SourceJson) :
    momentRecordsChunk014Push acc = momentJsonRecord014 :: acc := by rfl

noncomputable def momentTypedRecord014 : MomentRecord :=
  { simplexId := 14,
    factorFloorsQ80 := #[(394349507062555211031 : Int), (445000840426365780809 : Int), (201456169423530086932 : Int), (441173414679536330287 : Int), (392779061790584374488 : Int), (472563137694206670535 : Int), (352267711222097911052 : Int), (555868671002110916420 : Int), (491108567404813629142 : Int), (265339138692772206895 : Int)],
    oldFloorQ96 := (46226382184764416 : Int),
    newFloorQ96 := (46380042543308975 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_014_before_decode"
  err.flush

theorem decode_moment_record_014 :
    decodeMomentRecord momentJsonRecord014 = .ok momentTypedRecord014 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_014_decoded"
  err.flush

noncomputable def momentJsonRecord015 : SourceJson :=
  (momentRecordsChunk015Push []).head (List.cons_ne_nil _ _)

theorem moment_record_015_push_eq (acc : List SourceJson) :
    momentRecordsChunk015Push acc = momentJsonRecord015 :: acc := by rfl

noncomputable def momentTypedRecord015 : MomentRecord :=
  { simplexId := 15,
    factorFloorsQ80 := #[(473315312133434696942 : Int), (518522191488016817058 : Int), (205925669997385549308 : Int), (494573976810859420284 : Int), (356947377376628825163 : Int), (494500845999376412383 : Int), (229548438910474724428 : Int), (350341738175805579887 : Int), (326282614599964237355 : Int), (326299486802503354612 : Int)],
    oldFloorQ96 := (2586033715267 : Int),
    newFloorQ96 := (2594124201352 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_015_before_decode"
  err.flush

theorem decode_moment_record_015 :
    decodeMomentRecord momentJsonRecord015 = .ok momentTypedRecord015 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_015_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock003 : List SourceJson := [momentJsonRecord012, momentJsonRecord013, momentJsonRecord014, momentJsonRecord015]
noncomputable def momentTypedRecordsBlock003 : List MomentRecord := [momentTypedRecord012, momentTypedRecord013, momentTypedRecord014, momentTypedRecord015]

theorem moment_records_block_003_push_eq (acc : List SourceJson) :
    momentRecordsBlock003Push acc = [momentJsonRecord015, momentJsonRecord014, momentJsonRecord013, momentJsonRecord012] ++ acc := by rfl

theorem moment_records_block_003_reverse (acc : List SourceJson) :
    (momentRecordsBlock003Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock003 := by
  rw [moment_records_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_003 :
    momentJsonRecordsBlock003.mapM decodeMomentRecord = .ok momentTypedRecordsBlock003 := by
  simp only [momentJsonRecordsBlock003, momentTypedRecordsBlock003, List.mapM_cons, List.mapM_nil,
    decode_moment_record_012, decode_moment_record_013, decode_moment_record_014, decode_moment_record_015]
  rfl

noncomputable def momentTypedRowsThroughBlock003 : List MomentRecord := momentTypedRowsThroughBlock002 ++ momentTypedRecordsBlock003

theorem decode_moment_records_through_block_003 :
    momentRecordsAcc016.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock003 := by
  change (momentRecordsBlock003Push momentRecordsAcc012).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_003_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_002, decode_moment_records_block_003]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_block_003_complete"
  err.flush

#print axioms moment_record_012_push_eq
#print axioms decode_moment_record_012
#print axioms moment_record_013_push_eq
#print axioms decode_moment_record_013
#print axioms moment_record_014_push_eq
#print axioms decode_moment_record_014
#print axioms moment_record_015_push_eq
#print axioms decode_moment_record_015
#print axioms moment_records_block_003_push_eq
#print axioms moment_records_block_003_reverse
#print axioms decode_moment_records_block_003
#print axioms decode_moment_records_through_block_003

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
