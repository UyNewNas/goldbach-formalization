import ImbalancedChen.P2OriginalSaving19Moment00DecodedBlock000
import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock001

/-! Original typed moment records 4 through 7; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment00Parsing

noncomputable def momentJsonRecord004 : SourceJson :=
  (momentRecordsChunk004Push []).head (List.cons_ne_nil _ _)

theorem moment_record_004_push_eq (acc : List SourceJson) :
    momentRecordsChunk004Push acc = momentJsonRecord004 :: acc := by rfl

noncomputable def momentTypedRecord004 : MomentRecord :=
  { simplexId := 4,
    factorFloorsQ80 := #[(181838693816731049449 : Int), (208713505511779704136 : Int), (167774856012644706008 : Int), (496411685708366407253 : Int), (218359692641635916567 : Int), (419039785792122055070 : Int), (471858891779380975848 : Int), (606552796678711964096 : Int), (520185367391411090659 : Int), (414553487070891226196 : Int)],
    oldFloorQ96 := (68880418737607890 : Int),
    newFloorQ96 := (69091857154374035 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_004_before_decode"
  err.flush

theorem decode_moment_record_004 :
    decodeMomentRecord momentJsonRecord004 = .ok momentTypedRecord004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_004_decoded"
  err.flush

noncomputable def momentJsonRecord005 : SourceJson :=
  (momentRecordsChunk005Push []).head (List.cons_ne_nil _ _)

theorem moment_record_005_push_eq (acc : List SourceJson) :
    momentRecordsChunk005Push acc = momentJsonRecord005 :: acc := by rfl

noncomputable def momentTypedRecord005 : MomentRecord :=
  { simplexId := 5,
    factorFloorsQ80 := #[(171127900912761012192 : Int), (190482806824213760042 : Int), (163904398401058393049 : Int), (499155225595463076008 : Int), (234377648164330256600 : Int), (404380742005028091364 : Int), (590868395728562731173 : Int), (563048757480078976412 : Int), (368063354102993589627 : Int), (368122251109746225064 : Int)],
    oldFloorQ96 := (5059318791476 : Int),
    newFloorQ96 := (5074212093636 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_005_before_decode"
  err.flush

theorem decode_moment_record_005 :
    decodeMomentRecord momentJsonRecord005 = .ok momentTypedRecord005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_005_decoded"
  err.flush

noncomputable def momentJsonRecord006 : SourceJson :=
  (momentRecordsChunk006Push []).head (List.cons_ne_nil _ _)

theorem moment_record_006_push_eq (acc : List SourceJson) :
    momentRecordsChunk006Push acc = momentJsonRecord006 :: acc := by rfl

noncomputable def momentTypedRecord006 : MomentRecord :=
  { simplexId := 6,
    factorFloorsQ80 := #[(412447016560967183705 : Int), (450274931235986044512 : Int), (206784142673012590320 : Int), (573411891003671813455 : Int), (334866191889367809124 : Int), (510850788599231042459 : Int), (337095107265813814447 : Int), (547050459298154969798 : Int), (510836360093957476583 : Int), (425217855176749240268 : Int)],
    oldFloorQ96 := (6371508330372 : Int),
    newFloorQ96 := (6394258080032 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_006_before_decode"
  err.flush

theorem decode_moment_record_006 :
    decodeMomentRecord momentJsonRecord006 = .ok momentTypedRecord006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_006_decoded"
  err.flush

noncomputable def momentJsonRecord007 : SourceJson :=
  (momentRecordsChunk007Push []).head (List.cons_ne_nil _ _)

theorem moment_record_007_push_eq (acc : List SourceJson) :
    momentRecordsChunk007Push acc = momentJsonRecord007 :: acc := by rfl

noncomputable def momentTypedRecord007 : MomentRecord :=
  { simplexId := 7,
    factorFloorsQ80 := #[(340418543335370847968 : Int), (399862988522651603304 : Int), (199227626540148518825 : Int), (496844054926455854977 : Int), (329388984836673789548 : Int), (448735501447678872131 : Int), (331603852521540616807 : Int), (546000869374420994144 : Int), (525506874670950311147 : Int), (412873068775369638558 : Int)],
    oldFloorQ96 := (53311121843097312 : Int),
    newFloorQ96 := (53489153482388150 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_007_before_decode"
  err.flush

theorem decode_moment_record_007 :
    decodeMomentRecord momentJsonRecord007 = .ok momentTypedRecord007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 typed_record_007_decoded"
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
  err.putStrLn "P26_MOMENT00 typed_block_001_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment00Decoding
