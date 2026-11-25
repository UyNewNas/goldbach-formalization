import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock000

/-! Original typed moment records 0 through 3; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord000 : SourceJson :=
  (momentRecordsChunk000Push []).head (List.cons_ne_nil _ _)

theorem moment_record_000_push_eq (acc : List SourceJson) :
    momentRecordsChunk000Push acc = momentJsonRecord000 :: acc := by rfl

noncomputable def momentTypedRecord000 : MomentRecord :=
  { simplexId := 0,
    factorFloorsQ80 := #[(223715091813231429146 : Int), (243836725014720429762 : Int), (175451819875193653081 : Int), (540386383004951903861 : Int), (208681187597528508097 : Int), (443694450592304814666 : Int), (482220998682511591720 : Int), (542783189871415701929 : Int), (508195511639769104855 : Int), (424408015639575199546 : Int)],
    oldFloorQ96 := (6708449485921 : Int),
    newFloorQ96 := (6729532351297 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_000_before_decode"
  err.flush

theorem decode_moment_record_000 :
    decodeMomentRecord momentJsonRecord000 = .ok momentTypedRecord000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_000_decoded"
  err.flush

noncomputable def momentJsonRecord001 : SourceJson :=
  (momentRecordsChunk001Push []).head (List.cons_ne_nil _ _)

theorem moment_record_001_push_eq (acc : List SourceJson) :
    momentRecordsChunk001Push acc = momentJsonRecord001 :: acc := by rfl

noncomputable def momentTypedRecord001 : MomentRecord :=
  { simplexId := 1,
    factorFloorsQ80 := #[(178459725697957998627 : Int), (209155167736728192970 : Int), (169293705965297893700 : Int), (481332790212732918049 : Int), (206849971583466501343 : Int), (404516483868830182327 : Int), (470272366968661660334 : Int), (541618753542512940698 : Int), (522498076908367038196 : Int), (412492286372118010336 : Int)],
    oldFloorQ96 := (56087830196655987 : Int),
    newFloorQ96 := (56254936919881680 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_001_before_decode"
  err.flush

theorem decode_moment_record_001 :
    decodeMomentRecord momentJsonRecord001 = .ok momentTypedRecord001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_001_decoded"
  err.flush

noncomputable def momentJsonRecord002 : SourceJson :=
  (momentRecordsChunk002Push []).head (List.cons_ne_nil _ _)

theorem moment_record_002_push_eq (acc : List SourceJson) :
    momentRecordsChunk002Push acc = momentJsonRecord002 :: acc := by rfl

noncomputable def momentTypedRecord002 : MomentRecord :=
  { simplexId := 2,
    factorFloorsQ80 := #[(175801561521715166835 : Int), (192200178103954762472 : Int), (168742266297757256022 : Int), (501054351220854010748 : Int), (210162646193102457432 : Int), (404610645773674307336 : Int), (465787619630989759948 : Int), (559542628466749177422 : Int), (544968038767489584841 : Int), (412951138907472101461 : Int)],
    oldFloorQ96 := (63497001392343764 : Int),
    newFloorQ96 := (63688254849953009 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_002_before_decode"
  err.flush

theorem decode_moment_record_002 :
    decodeMomentRecord momentJsonRecord002 = .ok momentTypedRecord002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_002_decoded"
  err.flush

noncomputable def momentJsonRecord003 : SourceJson :=
  (momentRecordsChunk003Push []).head (List.cons_ne_nil _ _)

theorem moment_record_003_push_eq (acc : List SourceJson) :
    momentRecordsChunk003Push acc = momentJsonRecord003 :: acc := by rfl

noncomputable def momentTypedRecord003 : MomentRecord :=
  { simplexId := 3,
    factorFloorsQ80 := #[(190977801133708887629 : Int), (224138587590070657259 : Int), (167774856012644706008 : Int), (572824116911361208156 : Int), (218359692641635916567 : Int), (419039785792122055070 : Int), (471858891779380975848 : Int), (606552796678711964096 : Int), (615106840486394355833 : Int), (579415898385896136127 : Int)],
    oldFloorQ96 := (6593916892559 : Int),
    newFloorQ96 := (6616131927484 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_003_before_decode"
  err.flush

theorem decode_moment_record_003 :
    decodeMomentRecord momentJsonRecord003 = .ok momentTypedRecord003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_003_decoded"
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
  err.putStrLn "P26_MOMENT00 typed_block_000_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
