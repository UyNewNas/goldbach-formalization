import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock000

/-! Original typed moment records 0 through 3; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord000 : SourceJson :=
  (momentRecordsChunk000Push []).head (List.cons_ne_nil _ _)

theorem moment_record_000_push_eq (acc : List SourceJson) :
    momentRecordsChunk000Push acc = momentJsonRecord000 :: acc := by rfl

noncomputable def momentTypedRecord000 : MomentRecord :=
  { simplexId := 0,
    factorFloorsQ80 := #[(150512123208070358556 : Int), (161561114992623338854 : Int), (85345799592403673113 : Int), (287348395540234974187 : Int), (164863766045691710036 : Int), (203009276712255820887 : Int), (827765461165770339011 : Int), (497411832352664033164 : Int), (496911026411540772916 : Int), (380125099874362081579 : Int)],
    oldFloorQ96 := (2544973341103 : Int),
    newFloorQ96 := (2551834537496 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_000_before_decode"
  err.flush

theorem decode_moment_record_000 :
    decodeMomentRecord momentJsonRecord000 = .ok momentTypedRecord000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_000_decoded"
  err.flush

noncomputable def momentJsonRecord001 : SourceJson :=
  (momentRecordsChunk001Push []).head (List.cons_ne_nil _ _)

theorem moment_record_001_push_eq (acc : List SourceJson) :
    momentRecordsChunk001Push acc = momentJsonRecord001 :: acc := by rfl

noncomputable def momentTypedRecord001 : MomentRecord :=
  { simplexId := 1,
    factorFloorsQ80 := #[(192481549491734575531 : Int), (197327938247085619995 : Int), (80895095763382383803 : Int), (299152359798780182708 : Int), (165370316222015455687 : Int), (190164086970606311834 : Int), (682147364846382734295 : Int), (446969496377154183503 : Int), (466234399331643611474 : Int), (380258972852132961037 : Int)],
    oldFloorQ96 := (2532117028009 : Int),
    newFloorQ96 := (2538620469371 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_001_before_decode"
  err.flush

theorem decode_moment_record_001 :
    decodeMomentRecord momentJsonRecord001 = .ok momentTypedRecord001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_001_decoded"
  err.flush

noncomputable def momentJsonRecord002 : SourceJson :=
  (momentRecordsChunk002Push []).head (List.cons_ne_nil _ _)

theorem moment_record_002_push_eq (acc : List SourceJson) :
    momentRecordsChunk002Push acc = momentJsonRecord002 :: acc := by rfl

noncomputable def momentTypedRecord002 : MomentRecord :=
  { simplexId := 2,
    factorFloorsQ80 := #[(150298808297496418387 : Int), (160334111183253928437 : Int), (79882732258200035665 : Int), (276635375409804617169 : Int), (164607478836121679172 : Int), (179933254830755747064 : Int), (554294663236438486189 : Int), (450059815934548082635 : Int), (462425209144683801106 : Int), (370814214910603492971 : Int)],
    oldFloorQ96 := (13498229139073607 : Int),
    newFloorQ96 := (13530080282302287 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_002_before_decode"
  err.flush

theorem decode_moment_record_002 :
    decodeMomentRecord momentJsonRecord002 = .ok momentTypedRecord002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_002_decoded"
  err.flush

noncomputable def momentJsonRecord003 : SourceJson :=
  (momentRecordsChunk003Push []).head (List.cons_ne_nil _ _)

theorem moment_record_003_push_eq (acc : List SourceJson) :
    momentRecordsChunk003Push acc = momentJsonRecord003 :: acc := by rfl

noncomputable def momentTypedRecord003 : MomentRecord :=
  { simplexId := 3,
    factorFloorsQ80 := #[(149825028565801337569 : Int), (154076070366284549031 : Int), (79139967469834728627 : Int), (280015711032759933843 : Int), (165816356105663631476 : Int), (178382091858921800114 : Int), (556084395008604045708 : Int), (457474110295871146775 : Int), (457704025492398614324 : Int), (375277120124643515156 : Int)],
    oldFloorQ96 := (17749681913683967 : Int),
    newFloorQ96 := (17791631373674000 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_003_before_decode"
  err.flush

theorem decode_moment_record_003 :
    decodeMomentRecord momentJsonRecord003 = .ok momentTypedRecord003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_003_decoded"
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
  err.putStrLn "P26_MOMENT05 typed_block_000_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
