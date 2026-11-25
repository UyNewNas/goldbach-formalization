import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock012
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock013

/-! Original typed moment records 52 through 55; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord052 : SourceJson :=
  (momentRecordsChunk052Push []).head (List.cons_ne_nil _ _)

theorem moment_record_052_push_eq (acc : List SourceJson) :
    momentRecordsChunk052Push acc = momentJsonRecord052 :: acc := by rfl

noncomputable def momentTypedRecord052 : MomentRecord :=
  { simplexId := 52,
    factorFloorsQ80 := #[(2047764216921722112046 : Int), (2004700998847272853575 : Int), (205461689423160434067 : Int), (590652005917229527362 : Int), (1087637481354003285155 : Int), (1718867179266215423877 : Int), (1171247271182249433135 : Int), (1006630763244054409575 : Int), (936496820564266102836 : Int), (1855551247140094890818 : Int)],
    oldFloorQ96 := (43263342842337058 : Int),
    newFloorQ96 := (43717516348752600 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_052_before_decode"
  err.flush

theorem decode_moment_record_052 :
    decodeMomentRecord momentJsonRecord052 = .ok momentTypedRecord052 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_052_decoded"
  err.flush

noncomputable def momentJsonRecord053 : SourceJson :=
  (momentRecordsChunk053Push []).head (List.cons_ne_nil _ _)

theorem moment_record_053_push_eq (acc : List SourceJson) :
    momentRecordsChunk053Push acc = momentJsonRecord053 :: acc := by rfl

noncomputable def momentTypedRecord053 : MomentRecord :=
  { simplexId := 53,
    factorFloorsQ80 := #[(1935035621849866591558 : Int), (1899927765429695952310 : Int), (191841083810798551268 : Int), (641527348572921856195 : Int), (1146574693800715946979 : Int), (1726306501432858625124 : Int), (1159487635342543182666 : Int), (1020053192400366549420 : Int), (962648943651379412915 : Int), (1574937907362950279386 : Int)],
    oldFloorQ96 := (14464493985670685 : Int),
    newFloorQ96 := (14611908064959328 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_053_before_decode"
  err.flush

theorem decode_moment_record_053 :
    decodeMomentRecord momentJsonRecord053 = .ok momentTypedRecord053 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_053_decoded"
  err.flush

noncomputable def momentJsonRecord054 : SourceJson :=
  (momentRecordsChunk054Push []).head (List.cons_ne_nil _ _)

theorem moment_record_054_push_eq (acc : List SourceJson) :
    momentRecordsChunk054Push acc = momentJsonRecord054 :: acc := by rfl

noncomputable def momentTypedRecord054 : MomentRecord :=
  { simplexId := 54,
    factorFloorsQ80 := #[(1011984886279338863997 : Int), (994174909706229201647 : Int), (139949773564125208347 : Int), (595968047536225575871 : Int), (1110120271584207851373 : Int), (1314438149369699804356 : Int), (899793610544103864356 : Int), (794709526683793539229 : Int), (754604333879437562295 : Int), (1458374225774535454811 : Int)],
    oldFloorQ96 := (1809748772933864 : Int),
    newFloorQ96 := (1823383735574952 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_054_before_decode"
  err.flush

theorem decode_moment_record_054 :
    decodeMomentRecord momentJsonRecord054 = .ok momentTypedRecord054 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_054_decoded"
  err.flush

noncomputable def momentJsonRecord055 : SourceJson :=
  (momentRecordsChunk055Push []).head (List.cons_ne_nil _ _)

theorem moment_record_055_push_eq (acc : List SourceJson) :
    momentRecordsChunk055Push acc = momentJsonRecord055 :: acc := by rfl

noncomputable def momentTypedRecord055 : MomentRecord :=
  { simplexId := 55,
    factorFloorsQ80 := #[(1842230378913221447780 : Int), (1985761114829760646544 : Int), (261332996032402964246 : Int), (484555316673400623894 : Int), (911025887597396818555 : Int), (1765335035131542648523 : Int), (1926681331542794755321 : Int), (1014329314167185388738 : Int), (1014296035753193426668 : Int), (1636845685919718474227 : Int)],
    oldFloorQ96 := (1349163527900324 : Int),
    newFloorQ96 := (1363572057710335 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_055_before_decode"
  err.flush

theorem decode_moment_record_055 :
    decodeMomentRecord momentJsonRecord055 = .ok momentTypedRecord055 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_055_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock013 : List SourceJson := [momentJsonRecord052, momentJsonRecord053, momentJsonRecord054, momentJsonRecord055]
noncomputable def momentTypedRecordsBlock013 : List MomentRecord := [momentTypedRecord052, momentTypedRecord053, momentTypedRecord054, momentTypedRecord055]

theorem moment_records_block_013_push_eq (acc : List SourceJson) :
    momentRecordsBlock013Push acc = [momentJsonRecord055, momentJsonRecord054, momentJsonRecord053, momentJsonRecord052] ++ acc := by rfl

theorem moment_records_block_013_reverse (acc : List SourceJson) :
    (momentRecordsBlock013Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock013 := by
  rw [moment_records_block_013_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_013 :
    momentJsonRecordsBlock013.mapM decodeMomentRecord = .ok momentTypedRecordsBlock013 := by
  simp only [momentJsonRecordsBlock013, momentTypedRecordsBlock013, List.mapM_cons, List.mapM_nil,
    decode_moment_record_052, decode_moment_record_053, decode_moment_record_054, decode_moment_record_055]
  rfl

noncomputable def momentTypedRowsThroughBlock013 : List MomentRecord := momentTypedRowsThroughBlock012 ++ momentTypedRecordsBlock013

theorem decode_moment_records_through_block_013 :
    momentRecordsAcc056.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock013 := by
  change (momentRecordsBlock013Push momentRecordsAcc052).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_013_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_012, decode_moment_records_block_013]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_013_complete"
  err.flush

#print axioms moment_record_052_push_eq
#print axioms decode_moment_record_052
#print axioms moment_record_053_push_eq
#print axioms decode_moment_record_053
#print axioms moment_record_054_push_eq
#print axioms decode_moment_record_054
#print axioms moment_record_055_push_eq
#print axioms decode_moment_record_055
#print axioms moment_records_block_013_push_eq
#print axioms moment_records_block_013_reverse
#print axioms decode_moment_records_block_013
#print axioms decode_moment_records_through_block_013

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
