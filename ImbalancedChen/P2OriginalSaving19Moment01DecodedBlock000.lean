import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock000

/-! Original typed moment records 0 through 3; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord000 : SourceJson :=
  (momentRecordsChunk000Push []).head (List.cons_ne_nil _ _)

theorem moment_record_000_push_eq (acc : List SourceJson) :
    momentRecordsChunk000Push acc = momentJsonRecord000 :: acc := by rfl

noncomputable def momentTypedRecord000 : MomentRecord :=
  { simplexId := 0,
    factorFloorsQ80 := #[(1536304689398290994345 : Int), (1630629586612775166648 : Int), (285339855605409638981 : Int), (481827839027603771130 : Int), (650980477135048649316 : Int), (2158286574051371256495 : Int), (945994559030656125839 : Int), (692338205272114110890 : Int), (785191681593923200250 : Int), (785138180185780639258 : Int)],
    oldFloorQ96 := (561416098676369 : Int),
    newFloorQ96 := (566056822858902 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_000_before_decode"
  err.flush

theorem decode_moment_record_000 :
    decodeMomentRecord momentJsonRecord000 = .ok momentTypedRecord000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_000_decoded"
  err.flush

noncomputable def momentJsonRecord001 : SourceJson :=
  (momentRecordsChunk001Push []).head (List.cons_ne_nil _ _)

theorem moment_record_001_push_eq (acc : List SourceJson) :
    momentRecordsChunk001Push acc = momentJsonRecord001 :: acc := by rfl

noncomputable def momentTypedRecord001 : MomentRecord :=
  { simplexId := 1,
    factorFloorsQ80 := #[(1363057757103380590253 : Int), (1515880809131817953386 : Int), (269020878286272367745 : Int), (340794150216114092543 : Int), (637562604821060202088 : Int), (1720259233587676344742 : Int), (933011592457023292822 : Int), (696823687961429411992 : Int), (870787431432594701299 : Int), (740318940804572247540 : Int)],
    oldFloorQ96 := (6216170790303619159 : Int),
    newFloorQ96 := (6263073921870964900 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_001_before_decode"
  err.flush

theorem decode_moment_record_001 :
    decodeMomentRecord momentJsonRecord001 = .ok momentTypedRecord001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_001_decoded"
  err.flush

noncomputable def momentJsonRecord002 : SourceJson :=
  (momentRecordsChunk002Push []).head (List.cons_ne_nil _ _)

theorem moment_record_002_push_eq (acc : List SourceJson) :
    momentRecordsChunk002Push acc = momentJsonRecord002 :: acc := by rfl

noncomputable def momentTypedRecord002 : MomentRecord :=
  { simplexId := 2,
    factorFloorsQ80 := #[(1324082083326084512089 : Int), (1428886489545735975282 : Int), (248048807200228708858 : Int), (341131401547849698871 : Int), (710234483900946041956 : Int), (1768519819344605225502 : Int), (1131607744909232340543 : Int), (769905760558301070244 : Int), (923946627244056590763 : Int), (742036051485812125171 : Int)],
    oldFloorQ96 := (649894292267505 : Int),
    newFloorQ96 := (654960955602494 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_002_before_decode"
  err.flush

theorem decode_moment_record_002 :
    decodeMomentRecord momentJsonRecord002 = .ok momentTypedRecord002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_002_decoded"
  err.flush

noncomputable def momentJsonRecord003 : SourceJson :=
  (momentRecordsChunk003Push []).head (List.cons_ne_nil _ _)

theorem moment_record_003_push_eq (acc : List SourceJson) :
    momentRecordsChunk003Push acc = momentJsonRecord003 :: acc := by rfl

noncomputable def momentTypedRecord003 : MomentRecord :=
  { simplexId := 3,
    factorFloorsQ80 := #[(1077615173998865296118 : Int), (1239661678977924067817 : Int), (211885374675875752396 : Int), (175808098622745357399 : Int), (604094424828758284093 : Int), (1216060358131603605403 : Int), (1140760521633218364044 : Int), (762756760725016788082 : Int), (901079021473486370330 : Int), (667660461247906616883 : Int)],
    oldFloorQ96 := (283852627796034 : Int),
    newFloorQ96 := (285736616854906 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_003_before_decode"
  err.flush

theorem decode_moment_record_003 :
    decodeMomentRecord momentJsonRecord003 = .ok momentTypedRecord003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_003_decoded"
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
  err.putStrLn "P26_MOMENT01 typed_block_000_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
