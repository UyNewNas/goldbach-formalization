import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock010
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock011

/-! Original typed moment records 44 through 47; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord044 : SourceJson :=
  (momentRecordsChunk044Push []).head (List.cons_ne_nil _ _)

theorem moment_record_044_push_eq (acc : List SourceJson) :
    momentRecordsChunk044Push acc = momentJsonRecord044 :: acc := by rfl

noncomputable def momentTypedRecord044 : MomentRecord :=
  { simplexId := 44,
    factorFloorsQ80 := #[(519978283158804036690 : Int), (552308913473037754683 : Int), (186984904912657733888 : Int), (400122629794190406768 : Int), (431639218757022965227 : Int), (419379954055764622975 : Int), (1026766971895847639573 : Int), (358979154728284394637 : Int), (203902617463126790061 : Int), (203923204646701802027 : Int)],
    oldFloorQ96 := (1331929883767 : Int),
    newFloorQ96 := (1336680236462 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_044_before_decode"
  err.flush

theorem decode_moment_record_044 :
    decodeMomentRecord momentJsonRecord044 = .ok momentTypedRecord044 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_044_decoded"
  err.flush

noncomputable def momentJsonRecord045 : SourceJson :=
  (momentRecordsChunk045Push []).head (List.cons_ne_nil _ _)

theorem moment_record_045_push_eq (acc : List SourceJson) :
    momentRecordsChunk045Push acc = momentJsonRecord045 :: acc := by rfl

noncomputable def momentTypedRecord045 : MomentRecord :=
  { simplexId := 45,
    factorFloorsQ80 := #[(500935002866088555717 : Int), (539113502013806931743 : Int), (188217080298437974169 : Int), (395165488317723189330 : Int), (420438600697715976089 : Int), (414433919423894424301 : Int), (1322406274916971811171 : Int), (270915641476532622534 : Int), (228087637638181102699 : Int), (228104764361256518596 : Int)],
    oldFloorQ96 := (1183706265365 : Int),
    newFloorQ96 := (1188128284352 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_045_before_decode"
  err.flush

theorem decode_moment_record_045 :
    decodeMomentRecord momentJsonRecord045 = .ok momentTypedRecord045 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_045_decoded"
  err.flush

noncomputable def momentJsonRecord046 : SourceJson :=
  (momentRecordsChunk046Push []).head (List.cons_ne_nil _ _)

theorem moment_record_046_push_eq (acc : List SourceJson) :
    momentRecordsChunk046Push acc = momentJsonRecord046 :: acc := by rfl

noncomputable def momentTypedRecord046 : MomentRecord :=
  { simplexId := 46,
    factorFloorsQ80 := #[(375080657233075492582 : Int), (427219861964981463615 : Int), (168465012939425058539 : Int), (307070343980475509165 : Int), (375906458416860188466 : Int), (362174312185617183758 : Int), (1319638668049329842682 : Int), (259401290502966739273 : Int), (206864771014073868567 : Int), (206873531931671743020 : Int)],
    oldFloorQ96 := (860417513844 : Int),
    newFloorQ96 := (863275320433 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_046_before_decode"
  err.flush

theorem decode_moment_record_046 :
    decodeMomentRecord momentJsonRecord046 = .ok momentTypedRecord046 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_046_decoded"
  err.flush

noncomputable def momentJsonRecord047 : SourceJson :=
  (momentRecordsChunk047Push []).head (List.cons_ne_nil _ _)

theorem moment_record_047_push_eq (acc : List SourceJson) :
    momentRecordsChunk047Push acc = momentJsonRecord047 :: acc := by rfl

noncomputable def momentTypedRecord047 : MomentRecord :=
  { simplexId := 47,
    factorFloorsQ80 := #[(318731448368599209943 : Int), (384463602338711296666 : Int), (146680278042730154722 : Int), (236894318950242183580 : Int), (311206004586634160455 : Int), (325215936093541425013 : Int), (1398848547790955727442 : Int), (287602854312767259980 : Int), (251607299966752270345 : Int), (251608011773977656652 : Int)],
    oldFloorQ96 := (782138392973 : Int),
    newFloorQ96 := (784673994992 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_047_before_decode"
  err.flush

theorem decode_moment_record_047 :
    decodeMomentRecord momentJsonRecord047 = .ok momentTypedRecord047 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_047_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock011 : List SourceJson := [momentJsonRecord044, momentJsonRecord045, momentJsonRecord046, momentJsonRecord047]
noncomputable def momentTypedRecordsBlock011 : List MomentRecord := [momentTypedRecord044, momentTypedRecord045, momentTypedRecord046, momentTypedRecord047]

theorem moment_records_block_011_push_eq (acc : List SourceJson) :
    momentRecordsBlock011Push acc = [momentJsonRecord047, momentJsonRecord046, momentJsonRecord045, momentJsonRecord044] ++ acc := by rfl

theorem moment_records_block_011_reverse (acc : List SourceJson) :
    (momentRecordsBlock011Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock011 := by
  rw [moment_records_block_011_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_011 :
    momentJsonRecordsBlock011.mapM decodeMomentRecord = .ok momentTypedRecordsBlock011 := by
  simp only [momentJsonRecordsBlock011, momentTypedRecordsBlock011, List.mapM_cons, List.mapM_nil,
    decode_moment_record_044, decode_moment_record_045, decode_moment_record_046, decode_moment_record_047]
  rfl

noncomputable def momentTypedRowsThroughBlock011 : List MomentRecord := momentTypedRowsThroughBlock010 ++ momentTypedRecordsBlock011

theorem decode_moment_records_through_block_011 :
    momentRecordsAcc048.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock011 := by
  change (momentRecordsBlock011Push momentRecordsAcc044).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_011_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_010, decode_moment_records_block_011]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_block_011_complete"
  err.flush

#print axioms moment_record_044_push_eq
#print axioms decode_moment_record_044
#print axioms moment_record_045_push_eq
#print axioms decode_moment_record_045
#print axioms moment_record_046_push_eq
#print axioms decode_moment_record_046
#print axioms moment_record_047_push_eq
#print axioms decode_moment_record_047
#print axioms moment_records_block_011_push_eq
#print axioms moment_records_block_011_reverse
#print axioms decode_moment_records_block_011
#print axioms decode_moment_records_through_block_011

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
