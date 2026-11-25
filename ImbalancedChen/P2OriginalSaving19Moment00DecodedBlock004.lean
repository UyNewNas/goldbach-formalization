import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock003
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock004

/-! Original typed moment records 16 through 19; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord016 : SourceJson :=
  (momentRecordsChunk016Push []).head (List.cons_ne_nil _ _)

theorem moment_record_016_push_eq (acc : List SourceJson) :
    momentRecordsChunk016Push acc = momentJsonRecord016 :: acc := by rfl

noncomputable def momentTypedRecord016 : MomentRecord :=
  { simplexId := 16,
    factorFloorsQ80 := #[(390134862875640718316 : Int), (461567608133242695283 : Int), (195920350356128368319 : Int), (374081221907482617060 : Int), (346817664966436816379 : Int), (373412464750174527075 : Int), (231970937140936696974 : Int), (358199642654667840453 : Int), (388883720325879177263 : Int), (285272763044292621281 : Int)],
    oldFloorQ96 := (21656808638096986 : Int),
    newFloorQ96 := (21717914761676757 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_016_before_decode"
  err.flush

theorem decode_moment_record_016 :
    decodeMomentRecord momentJsonRecord016 = .ok momentTypedRecord016 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_016_decoded"
  err.flush

noncomputable def momentJsonRecord017 : SourceJson :=
  (momentRecordsChunk017Push []).head (List.cons_ne_nil _ _)

theorem moment_record_017_push_eq (acc : List SourceJson) :
    momentRecordsChunk017Push acc = momentJsonRecord017 :: acc := by rfl

noncomputable def momentTypedRecord017 : MomentRecord :=
  { simplexId := 17,
    factorFloorsQ80 := #[(382779631914668472868 : Int), (427631497004551633835 : Int), (194927592071530127760 : Int), (419893554109301725910 : Int), (359567544238503206688 : Int), (395552398477768694096 : Int), (257136890133950493108 : Int), (394643796116978556741 : Int), (526287784945051311991 : Int), (263484527312224177857 : Int)],
    oldFloorQ96 := (24481132133817717 : Int),
    newFloorQ96 := (24554586844781135 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_017_before_decode"
  err.flush

theorem decode_moment_record_017 :
    decodeMomentRecord momentJsonRecord017 = .ok momentTypedRecord017 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_017_decoded"
  err.flush

noncomputable def momentJsonRecord018 : SourceJson :=
  (momentRecordsChunk018Push []).head (List.cons_ne_nil _ _)

theorem moment_record_018_push_eq (acc : List SourceJson) :
    momentRecordsChunk018Push acc = momentJsonRecord018 :: acc := by rfl

noncomputable def momentTypedRecord018 : MomentRecord :=
  { simplexId := 18,
    factorFloorsQ80 := #[(448028019915147424911 : Int), (504515265124634089253 : Int), (190885177819330508824 : Int), (430811169501888885980 : Int), (355698697346513506747 : Int), (473147576771746047097 : Int), (267682200176943765609 : Int), (327255060764097741647 : Int), (337108768680991437934 : Int), (337115444038074528689 : Int)],
    oldFloorQ96 := (2582410192154 : Int),
    newFloorQ96 := (2590266478046 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_018_before_decode"
  err.flush

theorem decode_moment_record_018 :
    decodeMomentRecord momentJsonRecord018 = .ok momentTypedRecord018 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_018_decoded"
  err.flush

noncomputable def momentJsonRecord019 : SourceJson :=
  (momentRecordsChunk019Push []).head (List.cons_ne_nil _ _)

theorem moment_record_019_push_eq (acc : List SourceJson) :
    momentRecordsChunk019Push acc = momentJsonRecord019 :: acc := by rfl

noncomputable def momentTypedRecord019 : MomentRecord :=
  { simplexId := 19,
    factorFloorsQ80 := #[(347872801578590221796 : Int), (437619125783866939523 : Int), (179787973110433259904 : Int), (294379914874778330785 : Int), (343317529116154450141 : Int), (333104358438838951785 : Int), (275546812866761474970 : Int), (341283950032089734466 : Int), (408537946092382770587 : Int), (287149214710731378689 : Int)],
    oldFloorQ96 := (21636849119796108 : Int),
    newFloorQ96 := (21695069387400105 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_019_before_decode"
  err.flush

theorem decode_moment_record_019 :
    decodeMomentRecord momentJsonRecord019 = .ok momentTypedRecord019 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_019_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock004 : List SourceJson := [momentJsonRecord016, momentJsonRecord017, momentJsonRecord018, momentJsonRecord019]
noncomputable def momentTypedRecordsBlock004 : List MomentRecord := [momentTypedRecord016, momentTypedRecord017, momentTypedRecord018, momentTypedRecord019]

theorem moment_records_block_004_push_eq (acc : List SourceJson) :
    momentRecordsBlock004Push acc = [momentJsonRecord019, momentJsonRecord018, momentJsonRecord017, momentJsonRecord016] ++ acc := by rfl

theorem moment_records_block_004_reverse (acc : List SourceJson) :
    (momentRecordsBlock004Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock004 := by
  rw [moment_records_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_004 :
    momentJsonRecordsBlock004.mapM decodeMomentRecord = .ok momentTypedRecordsBlock004 := by
  simp only [momentJsonRecordsBlock004, momentTypedRecordsBlock004, List.mapM_cons, List.mapM_nil,
    decode_moment_record_016, decode_moment_record_017, decode_moment_record_018, decode_moment_record_019]
  rfl

noncomputable def momentTypedRowsThroughBlock004 : List MomentRecord := momentTypedRowsThroughBlock003 ++ momentTypedRecordsBlock004

theorem decode_moment_records_through_block_004 :
    momentRecordsAcc020.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock004 := by
  change (momentRecordsBlock004Push momentRecordsAcc016).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_004_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_003, decode_moment_records_block_004]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_block_004_complete"
  err.flush

#print axioms moment_record_016_push_eq
#print axioms decode_moment_record_016
#print axioms moment_record_017_push_eq
#print axioms decode_moment_record_017
#print axioms moment_record_018_push_eq
#print axioms decode_moment_record_018
#print axioms moment_record_019_push_eq
#print axioms decode_moment_record_019
#print axioms moment_records_block_004_push_eq
#print axioms moment_records_block_004_reverse
#print axioms decode_moment_records_block_004
#print axioms decode_moment_records_through_block_004

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
