import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock030
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock031

/-! Original typed moment records 124 through 127; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord124 : SourceJson :=
  (momentRecordsChunk124Push []).head (List.cons_ne_nil _ _)

theorem moment_record_124_push_eq (acc : List SourceJson) :
    momentRecordsChunk124Push acc = momentJsonRecord124 :: acc := by rfl

noncomputable def momentTypedRecord124 : MomentRecord :=
  { simplexId := 124,
    factorFloorsQ80 := #[(1643301244892965577946 : Int), (1742340909912877338327 : Int), (361176321280431787152 : Int), (638175775011167739048 : Int), (753593315558997306019 : Int), (2737844682406818230322 : Int), (2119200010408045015549 : Int), (1111779688758076690886 : Int), (1018615182892478021052 : Int), (1018644882441954265550 : Int)],
    oldFloorQ96 := (1070951830969694 : Int),
    newFloorQ96 := (1082659844092675 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_124_before_decode"
  err.flush

theorem decode_moment_record_124 :
    decodeMomentRecord momentJsonRecord124 = .ok momentTypedRecord124 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_124_decoded"
  err.flush

noncomputable def momentJsonRecord125 : SourceJson :=
  (momentRecordsChunk125Push []).head (List.cons_ne_nil _ _)

theorem moment_record_125_push_eq (acc : List SourceJson) :
    momentRecordsChunk125Push acc = momentJsonRecord125 :: acc := by rfl

noncomputable def momentTypedRecord125 : MomentRecord :=
  { simplexId := 125,
    factorFloorsQ80 := #[(1950071942850700789436 : Int), (2085731578072329989520 : Int), (351488423945062462944 : Int), (717813189147990206020 : Int), (877407295310240407679 : Int), (2645315454652145913265 : Int), (1558725758694953465637 : Int), (1241394879794323827324 : Int), (1367449500045047423283 : Int), (1367487149829030066285 : Int)],
    oldFloorQ96 := (225771511603418 : Int),
    newFloorQ96 := (228432038253216 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_125_before_decode"
  err.flush

theorem decode_moment_record_125 :
    decodeMomentRecord momentJsonRecord125 = .ok momentTypedRecord125 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_125_decoded"
  err.flush

noncomputable def momentJsonRecord126 : SourceJson :=
  (momentRecordsChunk126Push []).head (List.cons_ne_nil _ _)

theorem moment_record_126_push_eq (acc : List SourceJson) :
    momentRecordsChunk126Push acc = momentJsonRecord126 :: acc := by rfl

noncomputable def momentTypedRecord126 : MomentRecord :=
  { simplexId := 126,
    factorFloorsQ80 := #[(2186450112815265371447 : Int), (2364028148734785433505 : Int), (340795705744810205928 : Int), (800331892972999045926 : Int), (981533368987644523822 : Int), (2525767687483357028866 : Int), (1724468360388454373680 : Int), (1434994308497242316017 : Int), (1535690043529481674879 : Int), (1535734172107293898991 : Int)],
    oldFloorQ96 := (49257862802650 : Int),
    newFloorQ96 := (49890581172553 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_126_before_decode"
  err.flush

theorem decode_moment_record_126 :
    decodeMomentRecord momentJsonRecord126 = .ok momentTypedRecord126 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_126_decoded"
  err.flush

noncomputable def momentJsonRecord127 : SourceJson :=
  (momentRecordsChunk127Push []).head (List.cons_ne_nil _ _)

theorem moment_record_127_push_eq (acc : List SourceJson) :
    momentRecordsChunk127Push acc = momentJsonRecord127 :: acc := by rfl

noncomputable def momentTypedRecord127 : MomentRecord :=
  { simplexId := 127,
    factorFloorsQ80 := #[(2378600384935035320488 : Int), (2603134657443936452831 : Int), (322943287339525691328 : Int), (877455891718585617933 : Int), (1136233204242365730583 : Int), (2521782994892222114540 : Int), (1906274339396075655019 : Int), (1658868115434826427162 : Int), (1693897990717390629045 : Int), (1693947919756057954401 : Int)],
    oldFloorQ96 := (11313552016672 : Int),
    newFloorQ96 := (11471804680391 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_127_before_decode"
  err.flush

theorem decode_moment_record_127 :
    decodeMomentRecord momentJsonRecord127 = .ok momentTypedRecord127 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_127_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock031 : List SourceJson := [momentJsonRecord124, momentJsonRecord125, momentJsonRecord126, momentJsonRecord127]
noncomputable def momentTypedRecordsBlock031 : List MomentRecord := [momentTypedRecord124, momentTypedRecord125, momentTypedRecord126, momentTypedRecord127]

theorem moment_records_block_031_push_eq (acc : List SourceJson) :
    momentRecordsBlock031Push acc = [momentJsonRecord127, momentJsonRecord126, momentJsonRecord125, momentJsonRecord124] ++ acc := by rfl

theorem moment_records_block_031_reverse (acc : List SourceJson) :
    (momentRecordsBlock031Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock031 := by
  rw [moment_records_block_031_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_031 :
    momentJsonRecordsBlock031.mapM decodeMomentRecord = .ok momentTypedRecordsBlock031 := by
  simp only [momentJsonRecordsBlock031, momentTypedRecordsBlock031, List.mapM_cons, List.mapM_nil,
    decode_moment_record_124, decode_moment_record_125, decode_moment_record_126, decode_moment_record_127]
  rfl

noncomputable def momentTypedRowsThroughBlock031 : List MomentRecord := momentTypedRowsThroughBlock030 ++ momentTypedRecordsBlock031

theorem decode_moment_records_through_block_031 :
    momentRecordsAcc128.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock031 := by
  change (momentRecordsBlock031Push momentRecordsAcc124).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_031_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_030, decode_moment_records_block_031]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_031_complete"
  err.flush

#print axioms moment_record_124_push_eq
#print axioms decode_moment_record_124
#print axioms moment_record_125_push_eq
#print axioms decode_moment_record_125
#print axioms moment_record_126_push_eq
#print axioms decode_moment_record_126
#print axioms moment_record_127_push_eq
#print axioms decode_moment_record_127
#print axioms moment_records_block_031_push_eq
#print axioms moment_records_block_031_reverse
#print axioms decode_moment_records_block_031
#print axioms decode_moment_records_through_block_031

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
