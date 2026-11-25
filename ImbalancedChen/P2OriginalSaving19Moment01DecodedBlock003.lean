import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock002
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock003

/-! Original typed moment records 12 through 15; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord012 : SourceJson :=
  (momentRecordsChunk012Push []).head (List.cons_ne_nil _ _)

theorem moment_record_012_push_eq (acc : List SourceJson) :
    momentRecordsChunk012Push acc = momentJsonRecord012 :: acc := by rfl

noncomputable def momentTypedRecord012 : MomentRecord :=
  { simplexId := 12,
    factorFloorsQ80 := #[(1553486900299199464213 : Int), (1628161161559546634554 : Int), (294454463697135661381 : Int), (510903637324940473257 : Int), (680826218812855920609 : Int), (2092685763194154992283 : Int), (842423623274374033222 : Int), (909014475934742200064 : Int), (702422993990245598566 : Int), (702378379798313311837 : Int)],
    oldFloorQ96 := (625191386552427 : Int),
    newFloorQ96 := (630340891584692 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_012_before_decode"
  err.flush

theorem decode_moment_record_012 :
    decodeMomentRecord momentJsonRecord012 = .ok momentTypedRecord012 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_012_decoded"
  err.flush

noncomputable def momentJsonRecord013 : SourceJson :=
  (momentRecordsChunk013Push []).head (List.cons_ne_nil _ _)

theorem moment_record_013_push_eq (acc : List SourceJson) :
    momentRecordsChunk013Push acc = momentJsonRecord013 :: acc := by rfl

noncomputable def momentTypedRecord013 : MomentRecord :=
  { simplexId := 13,
    factorFloorsQ80 := #[(1408527301155389413633 : Int), (1529805333865137887171 : Int), (279078349238311810075 : Int), (382592513835650308710 : Int), (675511572111414877922 : Int), (1707728372132059629253 : Int), (818502222694779950809 : Int), (898532822494467638993 : Int), (776080573329950282271 : Int), (669181019077684081475 : Int)],
    oldFloorQ96 := (6917244893423826579 : Int),
    newFloorQ96 := (6969772378160762469 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_013_before_decode"
  err.flush

theorem decode_moment_record_013 :
    decodeMomentRecord momentJsonRecord013 = .ok momentTypedRecord013 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_013_decoded"
  err.flush

noncomputable def momentJsonRecord014 : SourceJson :=
  (momentRecordsChunk014Push []).head (List.cons_ne_nil _ _)

theorem moment_record_014_push_eq (acc : List SourceJson) :
    momentRecordsChunk014Push acc = momentJsonRecord014 :: acc := by rfl

noncomputable def momentTypedRecord014 : MomentRecord :=
  { simplexId := 14,
    factorFloorsQ80 := #[(1382512073941861068401 : Int), (1463990544494832676038 : Int), (268522203870457021369 : Int), (398425842297580408489 : Int), (719481842116980999845 : Int), (1707376661115011151812 : Int), (808210815835184132207 : Int), (941664690326233396049 : Int), (1007101999029300305076 : Int), (680898794773633939419 : Int)],
    oldFloorQ96 := (10207352316454701984 : Int),
    newFloorQ96 := (10286843297958040256 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_014_before_decode"
  err.flush

theorem decode_moment_record_014 :
    decodeMomentRecord momentJsonRecord014 = .ok momentTypedRecord014 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_014_decoded"
  err.flush

noncomputable def momentJsonRecord015 : SourceJson :=
  (momentRecordsChunk015Push []).head (List.cons_ne_nil _ _)

theorem moment_record_015_push_eq (acc : List SourceJson) :
    momentRecordsChunk015Push acc = momentJsonRecord015 :: acc := by rfl

noncomputable def momentTypedRecord015 : MomentRecord :=
  { simplexId := 15,
    factorFloorsQ80 := #[(1354881513790453928149 : Int), (1460182018664022817223 : Int), (268522355103566062104 : Int), (377016296516977035795 : Int), (768697587964250251646 : Int), (1802627075367397920733 : Int), (827998198448012228349 : Int), (981868104481672268295 : Int), (1260253974989434747335 : Int), (774131934231594857805 : Int)],
    oldFloorQ96 := (16508259086413636744 : Int),
    newFloorQ96 := (16643673762549791107 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_015_before_decode"
  err.flush

theorem decode_moment_record_015 :
    decodeMomentRecord momentJsonRecord015 = .ok momentTypedRecord015 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_015_decoded"
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
  err.putStrLn "P26_MOMENT01 typed_block_003_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
