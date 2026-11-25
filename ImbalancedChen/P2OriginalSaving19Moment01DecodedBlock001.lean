import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock000
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock001

/-! Original typed moment records 4 through 7; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord004 : SourceJson :=
  (momentRecordsChunk004Push []).head (List.cons_ne_nil _ _)

theorem moment_record_004_push_eq (acc : List SourceJson) :
    momentRecordsChunk004Push acc = momentJsonRecord004 :: acc := by rfl

noncomputable def momentTypedRecord004 : MomentRecord :=
  { simplexId := 4,
    factorFloorsQ80 := #[(1145018398878847334234 : Int), (1366540214674127026355 : Int), (232332982879120754887 : Int), (176442704182864880100 : Int), (569603514691512090750 : Int), (1127878550249907115788 : Int), (937742701977456253273 : Int), (695096631794636247500 : Int), (829934730044845584620 : Int), (683420248900872631636 : Int)],
    oldFloorQ96 := (2443699504783829963 : Int),
    newFloorQ96 := (2459444030579783698 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_004_before_decode"
  err.flush

theorem decode_moment_record_004 :
    decodeMomentRecord momentJsonRecord004 = .ok momentTypedRecord004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_004_decoded"
  err.flush

noncomputable def momentJsonRecord005 : SourceJson :=
  (momentRecordsChunk005Push []).head (List.cons_ne_nil _ _)

theorem moment_record_005_push_eq (acc : List SourceJson) :
    momentRecordsChunk005Push acc = momentJsonRecord005 :: acc := by rfl

noncomputable def momentTypedRecord005 : MomentRecord :=
  { simplexId := 5,
    factorFloorsQ80 := #[(1080587169573026032303 : Int), (1276224977901088612971 : Int), (219805567507596378090 : Int), (160335768736763670959 : Int), (481992845524443872741 : Int), (1095369353317332918346 : Int), (961953031783589031530 : Int), (670697292997694475344 : Int), (869815006265581181922 : Int), (658634189933465062187 : Int)],
    oldFloorQ96 := (1965718995760803648 : Int),
    newFloorQ96 := (1977911713569038876 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_005_before_decode"
  err.flush

theorem decode_moment_record_005 :
    decodeMomentRecord momentJsonRecord005 = .ok momentTypedRecord005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_005_decoded"
  err.flush

noncomputable def momentJsonRecord006 : SourceJson :=
  (momentRecordsChunk006Push []).head (List.cons_ne_nil _ _)

theorem moment_record_006_push_eq (acc : List SourceJson) :
    momentRecordsChunk006Push acc = momentJsonRecord006 :: acc := by rfl

noncomputable def momentTypedRecord006 : MomentRecord :=
  { simplexId := 6,
    factorFloorsQ80 := #[(1563016804111550273748 : Int), (1646167870406337640728 : Int), (290925972415402705444 : Int), (503330000497420774214 : Int), (553485704463449867525 : Int), (2133914925404650555354 : Int), (763187530204573259810 : Int), (707409285949700848107 : Int), (754371710643711166302 : Int), (754323270938933357207 : Int)],
    oldFloorQ96 := (433042752238305 : Int),
    newFloorQ96 := (436520528746544 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_006_before_decode"
  err.flush

theorem decode_moment_record_006 :
    decodeMomentRecord momentJsonRecord006 = .ok momentTypedRecord006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_006_decoded"
  err.flush

noncomputable def momentJsonRecord007 : SourceJson :=
  (momentRecordsChunk007Push []).head (List.cons_ne_nil _ _)

theorem moment_record_007_push_eq (acc : List SourceJson) :
    momentRecordsChunk007Push acc = momentJsonRecord007 :: acc := by rfl

noncomputable def momentTypedRecord007 : MomentRecord :=
  { simplexId := 7,
    factorFloorsQ80 := #[(1405830153060256572770 : Int), (1540722577755045729797 : Int), (274924856337088327064 : Int), (367292883923768956047 : Int), (544789133512056697319 : Int), (1662094839766524499724 : Int), (743511674577942695380 : Int), (702610223421951135174 : Int), (833184070574362141577 : Int), (716124558333731442966 : Int)],
    oldFloorQ96 := (4795220187265664527 : Int),
    newFloorQ96 := (4830217232844658444 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_007_before_decode"
  err.flush

theorem decode_moment_record_007 :
    decodeMomentRecord momentJsonRecord007 = .ok momentTypedRecord007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_007_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock001 : List SourceJson := [momentJsonRecord004, momentJsonRecord005, momentJsonRecord006, momentJsonRecord007]
noncomputable def momentTypedRecordsBlock001 : List MomentRecord := [momentTypedRecord004, momentTypedRecord005, momentTypedRecord006, momentTypedRecord007]

theorem moment_records_block_001_push_eq (acc : List SourceJson) :
    momentRecordsBlock001Push acc = [momentJsonRecord007, momentJsonRecord006, momentJsonRecord005, momentJsonRecord004] ++ acc := by rfl

theorem moment_records_block_001_reverse (acc : List SourceJson) :
    (momentRecordsBlock001Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock001 := by
  rw [moment_records_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_001 :
    momentJsonRecordsBlock001.mapM decodeMomentRecord = .ok momentTypedRecordsBlock001 := by
  simp only [momentJsonRecordsBlock001, momentTypedRecordsBlock001, List.mapM_cons, List.mapM_nil,
    decode_moment_record_004, decode_moment_record_005, decode_moment_record_006, decode_moment_record_007]
  rfl

noncomputable def momentTypedRowsThroughBlock001 : List MomentRecord := momentTypedRowsThroughBlock000 ++ momentTypedRecordsBlock001

theorem decode_moment_records_through_block_001 :
    momentRecordsAcc008.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock001 := by
  change (momentRecordsBlock001Push momentRecordsAcc004).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_001_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_000, decode_moment_records_block_001]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_001_complete"
  err.flush

#print axioms moment_record_004_push_eq
#print axioms decode_moment_record_004
#print axioms moment_record_005_push_eq
#print axioms decode_moment_record_005
#print axioms moment_record_006_push_eq
#print axioms decode_moment_record_006
#print axioms moment_record_007_push_eq
#print axioms decode_moment_record_007
#print axioms moment_records_block_001_push_eq
#print axioms moment_records_block_001_reverse
#print axioms decode_moment_records_block_001
#print axioms decode_moment_records_through_block_001

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
