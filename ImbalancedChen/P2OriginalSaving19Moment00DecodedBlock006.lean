import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock005
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock006

/-! Original typed moment records 24 through 27; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord024 : SourceJson :=
  (momentRecordsChunk024Push []).head (List.cons_ne_nil _ _)

theorem moment_record_024_push_eq (acc : List SourceJson) :
    momentRecordsChunk024Push acc = momentJsonRecord024 :: acc := by rfl

noncomputable def momentTypedRecord024 : MomentRecord :=
  { simplexId := 24,
    factorFloorsQ80 := #[(338403878157037603082 : Int), (396066322990023181059 : Int), (178669645975633218288 : Int), (346976747535281472639 : Int), (358624383175319539228 : Int), (360364312774165781313 : Int), (311956366318070950100 : Int), (390375498304926471041 : Int), (566856873492537597473 : Int), (258526476803857821642 : Int)],
    oldFloorQ96 := (24450152154923092 : Int),
    newFloorQ96 := (24521179486212018 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_024_before_decode"
  err.flush

theorem decode_moment_record_024 :
    decodeMomentRecord momentJsonRecord024 = .ok momentTypedRecord024 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_024_decoded"
  err.flush

noncomputable def momentJsonRecord025 : SourceJson :=
  (momentRecordsChunk025Push []).head (List.cons_ne_nil _ _)

theorem moment_record_025_push_eq (acc : List SourceJson) :
    momentRecordsChunk025Push acc = momentJsonRecord025 :: acc := by rfl

noncomputable def momentTypedRecord025 : MomentRecord :=
  { simplexId := 25,
    factorFloorsQ80 := #[(213695611812576966849 : Int), (295203845136178251324 : Int), (140602980159476079555 : Int), (193667530206437802586 : Int), (303523051414571841439 : Int), (193714434941606093194 : Int), (314749529771448861047 : Int), (378816051897202486060 : Int), (539007240171340276617 : Int), (207590269776939769034 : Int)],
    oldFloorQ96 := (16520640366052400 : Int),
    newFloorQ96 := (16558682133260946 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_025_before_decode"
  err.flush

theorem decode_moment_record_025 :
    decodeMomentRecord momentJsonRecord025 = .ok momentTypedRecord025 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_025_decoded"
  err.flush

noncomputable def momentJsonRecord026 : SourceJson :=
  (momentRecordsChunk026Push []).head (List.cons_ne_nil _ _)

theorem moment_record_026_push_eq (acc : List SourceJson) :
    momentRecordsChunk026Push acc = momentJsonRecord026 :: acc := by rfl

noncomputable def momentTypedRecord026 : MomentRecord :=
  { simplexId := 26,
    factorFloorsQ80 := #[(158449537168152973465 : Int), (246823049290681881096 : Int), (105631689480249419254 : Int), (91908649371689451780 : Int), (195042093555120570911 : Int), (119833301416894253929 : Int), (242431055232938270089 : Int), (257206704229719211346 : Int), (361282694706295207629 : Int), (180548755018737745031 : Int)],
    oldFloorQ96 := (15943554987400485 : Int),
    newFloorQ96 := (15969413695260587 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_026_before_decode"
  err.flush

theorem decode_moment_record_026 :
    decodeMomentRecord momentJsonRecord026 = .ok momentTypedRecord026 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_026_decoded"
  err.flush

noncomputable def momentJsonRecord027 : SourceJson :=
  (momentRecordsChunk027Push []).head (List.cons_ne_nil _ _)

theorem moment_record_027_push_eq (acc : List SourceJson) :
    momentRecordsChunk027Push acc = momentJsonRecord027 :: acc := by rfl

noncomputable def momentTypedRecord027 : MomentRecord :=
  { simplexId := 27,
    factorFloorsQ80 := #[(413027916390936752191 : Int), (477892941143732220021 : Int), (195226205329232372997 : Int), (400915885611117535263 : Int), (371251371563287438425 : Int), (423374061241669296414 : Int), (290485561934788998970 : Int), (448358257709835352040 : Int), (619701795988869101664 : Int), (354543073804381544004 : Int)],
    oldFloorQ96 := (52392041955377387 : Int),
    newFloorQ96 := (52565452682501541 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_027_before_decode"
  err.flush

theorem decode_moment_record_027 :
    decodeMomentRecord momentJsonRecord027 = .ok momentTypedRecord027 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_027_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock006 : List SourceJson := [momentJsonRecord024, momentJsonRecord025, momentJsonRecord026, momentJsonRecord027]
noncomputable def momentTypedRecordsBlock006 : List MomentRecord := [momentTypedRecord024, momentTypedRecord025, momentTypedRecord026, momentTypedRecord027]

theorem moment_records_block_006_push_eq (acc : List SourceJson) :
    momentRecordsBlock006Push acc = [momentJsonRecord027, momentJsonRecord026, momentJsonRecord025, momentJsonRecord024] ++ acc := by rfl

theorem moment_records_block_006_reverse (acc : List SourceJson) :
    (momentRecordsBlock006Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock006 := by
  rw [moment_records_block_006_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_006 :
    momentJsonRecordsBlock006.mapM decodeMomentRecord = .ok momentTypedRecordsBlock006 := by
  simp only [momentJsonRecordsBlock006, momentTypedRecordsBlock006, List.mapM_cons, List.mapM_nil,
    decode_moment_record_024, decode_moment_record_025, decode_moment_record_026, decode_moment_record_027]
  rfl

noncomputable def momentTypedRowsThroughBlock006 : List MomentRecord := momentTypedRowsThroughBlock005 ++ momentTypedRecordsBlock006

theorem decode_moment_records_through_block_006 :
    momentRecordsAcc028.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock006 := by
  change (momentRecordsBlock006Push momentRecordsAcc024).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_006_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_005, decode_moment_records_block_006]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_block_006_complete"
  err.flush

#print axioms moment_record_024_push_eq
#print axioms decode_moment_record_024
#print axioms moment_record_025_push_eq
#print axioms decode_moment_record_025
#print axioms moment_record_026_push_eq
#print axioms decode_moment_record_026
#print axioms moment_record_027_push_eq
#print axioms decode_moment_record_027
#print axioms moment_records_block_006_push_eq
#print axioms moment_records_block_006_reverse
#print axioms decode_moment_records_block_006
#print axioms decode_moment_records_through_block_006

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
