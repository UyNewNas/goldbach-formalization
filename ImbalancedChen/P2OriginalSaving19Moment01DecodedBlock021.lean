import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock020
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock021

/-! Original typed moment records 84 through 87; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord084 : SourceJson :=
  (momentRecordsChunk084Push []).head (List.cons_ne_nil _ _)

theorem moment_record_084_push_eq (acc : List SourceJson) :
    momentRecordsChunk084Push acc = momentJsonRecord084 :: acc := by rfl

noncomputable def momentTypedRecord084 : MomentRecord :=
  { simplexId := 84,
    factorFloorsQ80 := #[(1004825794288494157638 : Int), (1049174135537894925718 : Int), (295788633830144618716 : Int), (570817124344850737001 : Int), (1320731454679816086676 : Int), (1974817987513398954448 : Int), (1304551085995126194077 : Int), (1004620036253611047651 : Int), (1100921501515725576599 : Int), (1335538634766720172143 : Int)],
    oldFloorQ96 := (3043104331023334927 : Int),
    newFloorQ96 := (3070822781848213411 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_084_before_decode"
  err.flush

theorem decode_moment_record_084 :
    decodeMomentRecord momentJsonRecord084 = .ok momentTypedRecord084 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_084_decoded"
  err.flush

noncomputable def momentJsonRecord085 : SourceJson :=
  (momentRecordsChunk085Push []).head (List.cons_ne_nil _ _)

theorem moment_record_085_push_eq (acc : List SourceJson) :
    momentRecordsChunk085Push acc = momentJsonRecord085 :: acc := by rfl

noncomputable def momentTypedRecord085 : MomentRecord :=
  { simplexId := 85,
    factorFloorsQ80 := #[(1022281548532702418063 : Int), (1087174294706823404171 : Int), (295788783900309997839 : Int), (559992783445236608820 : Int), (1317773437317275220427 : Int), (2060632937097330071214 : Int), (1314374431011582290117 : Int), (1020410055708469950925 : Int), (1056118347549083158632 : Int), (1564152318567474472638 : Int)],
    oldFloorQ96 := (4926678996932180061 : Int),
    newFloorQ96 := (4972939898024792251 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_085_before_decode"
  err.flush

theorem decode_moment_record_085 :
    decodeMomentRecord momentJsonRecord085 = .ok momentTypedRecord085 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_085_decoded"
  err.flush

noncomputable def momentJsonRecord086 : SourceJson :=
  (momentRecordsChunk086Push []).head (List.cons_ne_nil _ _)

theorem moment_record_086_push_eq (acc : List SourceJson) :
    momentRecordsChunk086Push acc = momentJsonRecord086 :: acc := by rfl

noncomputable def momentTypedRecord086 : MomentRecord :=
  { simplexId := 86,
    factorFloorsQ80 := #[(1514422590509313689719 : Int), (1584308993179996386606 : Int), (318059749723858097688 : Int), (712651763673827662002 : Int), (1415173279890665450429 : Int), (2310670236641715351026 : Int), (1540128843012962481206 : Int), (1248022602011716577537 : Int), (1337129333994699934617 : Int), (1337203769249296024422 : Int)],
    oldFloorQ96 := (40441945864525 : Int),
    newFloorQ96 := (40889925475588 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_086_before_decode"
  err.flush

theorem decode_moment_record_086 :
    decodeMomentRecord momentJsonRecord086 = .ok momentTypedRecord086 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_086_decoded"
  err.flush

noncomputable def momentJsonRecord087 : SourceJson :=
  (momentRecordsChunk087Push []).head (List.cons_ne_nil _ _)

theorem moment_record_087_push_eq (acc : List SourceJson) :
    momentRecordsChunk087Push acc = momentJsonRecord087 :: acc := by rfl

noncomputable def momentTypedRecord087 : MomentRecord :=
  { simplexId := 87,
    factorFloorsQ80 := #[(1376432148999172748122 : Int), (1490000434650424713918 : Int), (302144965935948552514 : Int), (633668873377383369169 : Int), (1435603144051975190355 : Int), (1895699457108670974613 : Int), (1506181913555134262452 : Int), (1217944270711389909186 : Int), (1285318003044319063659 : Int), (1426252282910722874256 : Int)],
    oldFloorQ96 := (447295798978627441 : Int),
    newFloorQ96 := (451970609344687757 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_087_before_decode"
  err.flush

theorem decode_moment_record_087 :
    decodeMomentRecord momentJsonRecord087 = .ok momentTypedRecord087 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_087_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock021 : List SourceJson := [momentJsonRecord084, momentJsonRecord085, momentJsonRecord086, momentJsonRecord087]
noncomputable def momentTypedRecordsBlock021 : List MomentRecord := [momentTypedRecord084, momentTypedRecord085, momentTypedRecord086, momentTypedRecord087]

theorem moment_records_block_021_push_eq (acc : List SourceJson) :
    momentRecordsBlock021Push acc = [momentJsonRecord087, momentJsonRecord086, momentJsonRecord085, momentJsonRecord084] ++ acc := by rfl

theorem moment_records_block_021_reverse (acc : List SourceJson) :
    (momentRecordsBlock021Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock021 := by
  rw [moment_records_block_021_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_021 :
    momentJsonRecordsBlock021.mapM decodeMomentRecord = .ok momentTypedRecordsBlock021 := by
  simp only [momentJsonRecordsBlock021, momentTypedRecordsBlock021, List.mapM_cons, List.mapM_nil,
    decode_moment_record_084, decode_moment_record_085, decode_moment_record_086, decode_moment_record_087]
  rfl

noncomputable def momentTypedRowsThroughBlock021 : List MomentRecord := momentTypedRowsThroughBlock020 ++ momentTypedRecordsBlock021

theorem decode_moment_records_through_block_021 :
    momentRecordsAcc088.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock021 := by
  change (momentRecordsBlock021Push momentRecordsAcc084).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_021_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_020, decode_moment_records_block_021]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_021_complete"
  err.flush

#print axioms moment_record_084_push_eq
#print axioms decode_moment_record_084
#print axioms moment_record_085_push_eq
#print axioms decode_moment_record_085
#print axioms moment_record_086_push_eq
#print axioms decode_moment_record_086
#print axioms moment_record_087_push_eq
#print axioms decode_moment_record_087
#print axioms moment_records_block_021_push_eq
#print axioms moment_records_block_021_reverse
#print axioms decode_moment_records_block_021
#print axioms decode_moment_records_through_block_021

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
