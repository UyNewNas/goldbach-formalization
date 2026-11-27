import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock012
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock013

/-! Original typed moment records 52 through 55; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord052 : SourceJson :=
  (momentRecordsChunk052Push []).head (List.cons_ne_nil _ _)

theorem moment_record_052_push_eq (acc : List SourceJson) :
    momentRecordsChunk052Push acc = momentJsonRecord052 :: acc := by rfl

noncomputable def momentTypedRecord052 : MomentRecord :=
  { simplexId := 52,
    factorFloorsQ80 := #[(388110538363424127545 : Int), (421324334762982423459 : Int), (188217080298437974169 : Int), (434128015334831053789 : Int), (382326085875767258044 : Int), (414433919423894424301 : Int), (1209716744357084676485 : Int), (367258101518558191927 : Int), (272179435559236857342 : Int), (272201109762655002069 : Int)],
    oldFloorQ96 := (1195632320589 : Int),
    newFloorQ96 := (1199942132978 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_052_before_decode"
  err.flush

theorem decode_moment_record_052 :
    decodeMomentRecord momentJsonRecord052 = .ok momentTypedRecord052 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_052_decoded"
  err.flush

noncomputable def momentJsonRecord053 : SourceJson :=
  (momentRecordsChunk053Push []).head (List.cons_ne_nil _ _)

theorem moment_record_053_push_eq (acc : List SourceJson) :
    momentRecordsChunk053Push acc = momentJsonRecord053 :: acc := by rfl

noncomputable def momentTypedRecord053 : MomentRecord :=
  { simplexId := 53,
    factorFloorsQ80 := #[(280462276196236998337 : Int), (327067788459463727804 : Int), (168465012939425058539 : Int), (336225834812233586751 : Int), (346919349969073751257 : Int), (362174312185617183758 : Int), (1206703329901137760610 : Int), (344382053183791276311 : Int), (223841151033575717193 : Int), (223858834280279972059 : Int)],
    oldFloorQ96 := (869314510000 : Int),
    newFloorQ96 := (872065812528 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_053_before_decode"
  err.flush

theorem decode_moment_record_053 :
    decodeMomentRecord momentJsonRecord053 = .ok momentTypedRecord053 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_053_decoded"
  err.flush

noncomputable def momentJsonRecord054 : SourceJson :=
  (momentRecordsChunk054Push []).head (List.cons_ne_nil _ _)

theorem moment_record_054_push_eq (acc : List SourceJson) :
    momentRecordsChunk054Push acc = momentJsonRecord054 :: acc := by rfl

noncomputable def momentTypedRecord054 : MomentRecord :=
  { simplexId := 54,
    factorFloorsQ80 := #[(241709641202653311261 : Int), (301341599418728636551 : Int), (146680278042730154722 : Int), (258646493244514655980 : Int), (292437350046219538124 : Int), (325215936093541425013 : Int), (1276136354560244491050 : Int), (334865250921330481420 : Int), (242447947926414891690 : Int), (242461797208609845083 : Int)],
    oldFloorQ96 := (790681081021 : Int),
    newFloorQ96 := (793079754626 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_054_before_decode"
  err.flush

theorem decode_moment_record_054 :
    decodeMomentRecord momentJsonRecord054 = .ok momentTypedRecord054 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_054_decoded"
  err.flush

noncomputable def momentJsonRecord055 : SourceJson :=
  (momentRecordsChunk055Push []).head (List.cons_ne_nil _ _)

theorem moment_record_055_push_eq (acc : List SourceJson) :
    momentRecordsChunk055Push acc = momentJsonRecord055 :: acc := by rfl

noncomputable def momentTypedRecord055 : MomentRecord :=
  { simplexId := 55,
    factorFloorsQ80 := #[(199445363444041675426 : Int), (256942882153795981310 : Int), (88173380080299264726 : Int), (128616043265695749409 : Int), (202473762103519005043 : Int), (144255522689224992128 : Int), (621670653641986827864 : Int), (326034441372303914373 : Int), (225648961725508575655 : Int), (225660415668076807628 : Int)],
    oldFloorQ96 := (917467481216 : Int),
    newFloorQ96 := (919305065836 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_055_before_decode"
  err.flush

theorem decode_moment_record_055 :
    decodeMomentRecord momentJsonRecord055 = .ok momentTypedRecord055 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_055_decoded"
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
  err.putStrLn "P26_MOMENT05 typed_block_013_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
