import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock028
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock029

/-! Original typed moment records 116 through 119; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord116 : SourceJson :=
  (momentRecordsChunk116Push []).head (List.cons_ne_nil _ _)

theorem moment_record_116_push_eq (acc : List SourceJson) :
    momentRecordsChunk116Push acc = momentJsonRecord116 :: acc := by rfl

noncomputable def momentTypedRecord116 : MomentRecord :=
  { simplexId := 116,
    factorFloorsQ80 := #[(1368214108085883920992 : Int), (1334472002014113977127 : Int), (138992145546194885064 : Int), (745846536750490334103 : Int), (798698134537634998987 : Int), (1357648046352872336346 : Int), (1109528038255584648649 : Int), (1015135235552250178365 : Int), (953381991988452205820 : Int), (910219058538005688680 : Int)],
    oldFloorQ96 := (317391285706715 : Int),
    newFloorQ96 := (319956671779794 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_116_before_decode"
  err.flush

theorem decode_moment_record_116 :
    decodeMomentRecord momentJsonRecord116 = .ok momentTypedRecord116 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_116_decoded"
  err.flush

noncomputable def momentJsonRecord117 : SourceJson :=
  (momentRecordsChunk117Push []).head (List.cons_ne_nil _ _)

theorem moment_record_117_push_eq (acc : List SourceJson) :
    momentRecordsChunk117Push acc = momentJsonRecord117 :: acc := by rfl

noncomputable def momentTypedRecord117 : MomentRecord :=
  { simplexId := 117,
    factorFloorsQ80 := #[(1320783805854573208207 : Int), (1285744872857855898799 : Int), (144502079199801448750 : Int), (715983024925672095036 : Int), (806944801403228910886 : Int), (1424657212451831954575 : Int), (1154023831390712304430 : Int), (950466114283182096318 : Int), (950461071861409447695 : Int), (958650489547272347181 : Int)],
    oldFloorQ96 := (333257254845 : Int),
    newFloorQ96 := (335945346157 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_117_before_decode"
  err.flush

theorem decode_moment_record_117 :
    decodeMomentRecord momentJsonRecord117 = .ok momentTypedRecord117 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_117_decoded"
  err.flush

noncomputable def momentJsonRecord118 : SourceJson :=
  (momentRecordsChunk118Push []).head (List.cons_ne_nil _ _)

theorem moment_record_118_push_eq (acc : List SourceJson) :
    momentRecordsChunk118Push acc = momentJsonRecord118 :: acc := by rfl

noncomputable def momentTypedRecord118 : MomentRecord :=
  { simplexId := 118,
    factorFloorsQ80 := #[(1380293126749044395262 : Int), (1350218004972426023578 : Int), (130502633969703621525 : Int), (739445101464181566158 : Int), (821727018078504210069 : Int), (1342557983857557411451 : Int), (1116138020165294509042 : Int), (1024422119954241055965 : Int), (945875358690578487181 : Int), (945961367144141544141 : Int)],
    oldFloorQ96 := (52999559636 : Int),
    newFloorQ96 := (53430813398 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_118_before_decode"
  err.flush

theorem decode_moment_record_118 :
    decodeMomentRecord momentJsonRecord118 = .ok momentTypedRecord118 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_118_decoded"
  err.flush

noncomputable def momentJsonRecord119 : SourceJson :=
  (momentRecordsChunk119Push []).head (List.cons_ne_nil _ _)

theorem moment_record_119_push_eq (acc : List SourceJson) :
    momentRecordsChunk119Push acc = momentJsonRecord119 :: acc := by rfl

noncomputable def momentTypedRecord119 : MomentRecord :=
  { simplexId := 119,
    factorFloorsQ80 := #[(1359949449112158234051 : Int), (1482834047809614851300 : Int), (327223110608084868645 : Int), (461792835196072244944 : Int), (732595360835807739475 : Int), (2584709838347898995343 : Int), (1130319934205268932331 : Int), (791242327747567129920 : Int), (760427267889702950986 : Int), (760440719022778516309 : Int)],
    oldFloorQ96 := (630059312594462 : Int),
    newFloorQ96 := (635498441292170 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_119_before_decode"
  err.flush

theorem decode_moment_record_119 :
    decodeMomentRecord momentJsonRecord119 = .ok momentTypedRecord119 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_119_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock029 : List SourceJson := [momentJsonRecord116, momentJsonRecord117, momentJsonRecord118, momentJsonRecord119]
noncomputable def momentTypedRecordsBlock029 : List MomentRecord := [momentTypedRecord116, momentTypedRecord117, momentTypedRecord118, momentTypedRecord119]

theorem moment_records_block_029_push_eq (acc : List SourceJson) :
    momentRecordsBlock029Push acc = [momentJsonRecord119, momentJsonRecord118, momentJsonRecord117, momentJsonRecord116] ++ acc := by rfl

theorem moment_records_block_029_reverse (acc : List SourceJson) :
    (momentRecordsBlock029Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock029 := by
  rw [moment_records_block_029_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_029 :
    momentJsonRecordsBlock029.mapM decodeMomentRecord = .ok momentTypedRecordsBlock029 := by
  simp only [momentJsonRecordsBlock029, momentTypedRecordsBlock029, List.mapM_cons, List.mapM_nil,
    decode_moment_record_116, decode_moment_record_117, decode_moment_record_118, decode_moment_record_119]
  rfl

noncomputable def momentTypedRowsThroughBlock029 : List MomentRecord := momentTypedRowsThroughBlock028 ++ momentTypedRecordsBlock029

theorem decode_moment_records_through_block_029 :
    momentRecordsAcc120.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock029 := by
  change (momentRecordsBlock029Push momentRecordsAcc116).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_029_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_028, decode_moment_records_block_029]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_029_complete"
  err.flush

#print axioms moment_record_116_push_eq
#print axioms decode_moment_record_116
#print axioms moment_record_117_push_eq
#print axioms decode_moment_record_117
#print axioms moment_record_118_push_eq
#print axioms decode_moment_record_118
#print axioms moment_record_119_push_eq
#print axioms decode_moment_record_119
#print axioms moment_records_block_029_push_eq
#print axioms moment_records_block_029_reverse
#print axioms decode_moment_records_block_029
#print axioms decode_moment_records_through_block_029

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
