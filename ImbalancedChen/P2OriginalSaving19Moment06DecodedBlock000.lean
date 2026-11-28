/- SOURCE_CANDIDATE: original Cell06 source only. No Lean compilation,
independent kernel replay, full-owned audit or formal acceptance is claimed. -/

import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalSaving19Moment06RecordsBlock000

/-! Original typed moment records 0 through 3; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment06Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment06Parsing

noncomputable def momentJsonRecord000 : SourceJson :=
  (momentRecordsChunk000Push []).head (List.cons_ne_nil _ _)

theorem moment_record_000_push_eq (acc : List SourceJson) :
    momentRecordsChunk000Push acc = momentJsonRecord000 :: acc := by rfl

noncomputable def momentTypedRecord000 : MomentRecord :=
  { simplexId := 0,
    factorFloorsQ80 := #[(84396131268658059303 : Int), (177210546529521561254 : Int), (187546035050209118385 : Int), (38108991669890625047 : Int), (139441982008320462738 : Int), (92094588392885582934 : Int), (97997240474552334736 : Int), (93991918924974465961 : Int), (109400919321435756291 : Int), (24596776163698111096 : Int)],
    oldFloorQ96 := (6678443759985 : Int),
    newFloorQ96 := (6684217939485 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_000_before_decode"
  err.flush

theorem decode_moment_record_000 :
    decodeMomentRecord momentJsonRecord000 = .ok momentTypedRecord000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_000_decoded"
  err.flush

noncomputable def momentJsonRecord001 : SourceJson :=
  (momentRecordsChunk001Push []).head (List.cons_ne_nil _ _)

theorem moment_record_001_push_eq (acc : List SourceJson) :
    momentRecordsChunk001Push acc = momentJsonRecord001 :: acc := by rfl

noncomputable def momentTypedRecord001 : MomentRecord :=
  { simplexId := 1,
    factorFloorsQ80 := #[(92047653990312629910 : Int), (178341037072827851576 : Int), (191593149102226458975 : Int), (145756396517730706202 : Int), (235356053958587228240 : Int), (118755938013610571934 : Int), (123730944240216849658 : Int), (124188725220156365551 : Int), (145090189582006084706 : Int), (300828793827249631124 : Int)],
    oldFloorQ96 := (81101014145393 : Int),
    newFloorQ96 := (81212162437289 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_001_before_decode"
  err.flush

theorem decode_moment_record_001 :
    decodeMomentRecord momentJsonRecord001 = .ok momentTypedRecord001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_001_decoded"
  err.flush

noncomputable def momentJsonRecord002 : SourceJson :=
  (momentRecordsChunk002Push []).head (List.cons_ne_nil _ _)

theorem moment_record_002_push_eq (acc : List SourceJson) :
    momentRecordsChunk002Push acc = momentJsonRecord002 :: acc := by rfl

noncomputable def momentTypedRecord002 : MomentRecord :=
  { simplexId := 2,
    factorFloorsQ80 := #[(265428010155675791132 : Int), (259939612984311871083 : Int), (184818298489773060707 : Int), (204266100769654779191 : Int), (283205656442225473585 : Int), (162476754477464836486 : Int), (142092307891584324461 : Int), (139626094512983424921 : Int), (158002353587055281709 : Int), (322237779935573720078 : Int)],
    oldFloorQ96 := (839187394217042 : Int),
    newFloorQ96 := (840661758939561 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_002_before_decode"
  err.flush

theorem decode_moment_record_002 :
    decodeMomentRecord momentJsonRecord002 = .ok momentTypedRecord002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_002_decoded"
  err.flush

noncomputable def momentJsonRecord003 : SourceJson :=
  (momentRecordsChunk003Push []).head (List.cons_ne_nil _ _)

theorem moment_record_003_push_eq (acc : List SourceJson) :
    momentRecordsChunk003Push acc = momentJsonRecord003 :: acc := by rfl

noncomputable def momentTypedRecord003 : MomentRecord :=
  { simplexId := 3,
    factorFloorsQ80 := #[(397856198486089570856 : Int), (323306646743891851328 : Int), (175270596458546008425 : Int), (249685334694149527583 : Int), (317217417172225112527 : Int), (192630712353306862463 : Int), (158208739301260474836 : Int), (152496163247169964386 : Int), (152505490534367412682 : Int), (336318965881512432091 : Int)],
    oldFloorQ96 := (229654068608 : Int),
    newFloorQ96 := (230121001964 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_003_before_decode"
  err.flush

theorem decode_moment_record_003 :
    decodeMomentRecord momentJsonRecord003 = .ok momentTypedRecord003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_003_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock000 : List SourceJson := [momentJsonRecord000, momentJsonRecord001, momentJsonRecord002, momentJsonRecord003]
noncomputable def momentTypedRecordsBlock000 : List MomentRecord := [momentTypedRecord000, momentTypedRecord001, momentTypedRecord002, momentTypedRecord003]

theorem moment_records_block_000_push_eq (acc : List SourceJson) :
    momentRecordsBlock000Push acc = [momentJsonRecord003, momentJsonRecord002, momentJsonRecord001, momentJsonRecord000] ++ acc := by rfl

theorem moment_records_block_000_reverse (acc : List SourceJson) :
    (momentRecordsBlock000Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock000 := by
  rw [moment_records_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_000 :
    momentJsonRecordsBlock000.mapM decodeMomentRecord = .ok momentTypedRecordsBlock000 := by
  simp only [momentJsonRecordsBlock000, momentTypedRecordsBlock000, List.mapM_cons, List.mapM_nil,
    decode_moment_record_000, decode_moment_record_001, decode_moment_record_002, decode_moment_record_003]
  rfl

noncomputable def momentTypedRowsThroughBlock000 : List MomentRecord := momentTypedRecordsBlock000

theorem decode_moment_records_through_block_000 :
    momentRecordsAcc004.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock000 := by
  change (momentRecordsBlock000Push momentRecordsAcc000).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_000_reverse]
  exact decode_moment_records_block_000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_block_000_complete"
  err.flush

#print axioms moment_record_000_push_eq
#print axioms decode_moment_record_000
#print axioms moment_record_001_push_eq
#print axioms decode_moment_record_001
#print axioms moment_record_002_push_eq
#print axioms decode_moment_record_002
#print axioms moment_record_003_push_eq
#print axioms decode_moment_record_003
#print axioms moment_records_block_000_push_eq
#print axioms moment_records_block_000_reverse
#print axioms decode_moment_records_block_000
#print axioms decode_moment_records_through_block_000

end ImbalancedChen.P2OriginalSaving19Moment06Decoding
