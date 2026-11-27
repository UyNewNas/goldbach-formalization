import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock001
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock002

/-! Original typed moment records 8 through 11; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord008 : SourceJson :=
  (momentRecordsChunk008Push []).head (List.cons_ne_nil _ _)

theorem moment_record_008_push_eq (acc : List SourceJson) :
    momentRecordsChunk008Push acc = momentJsonRecord008 :: acc := by rfl

noncomputable def momentTypedRecord008 : MomentRecord :=
  { simplexId := 8,
    factorFloorsQ80 := #[(385407910404890136003 : Int), (401741042747992577605 : Int), (136831982567153581605 : Int), (388945941442331164483 : Int), (313898886976379555397 : Int), (312683174559306100785 : Int), (831096365367886114153 : Int), (450753014885983327563 : Int), (468837625533390474266 : Int), (381021792422303865217 : Int)],
    oldFloorQ96 := (2395173826670 : Int),
    newFloorQ96 := (2403253488625 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_008_before_decode"
  err.flush

theorem decode_moment_record_008 :
    decodeMomentRecord momentJsonRecord008 = .ok momentTypedRecord008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_008_decoded"
  err.flush

noncomputable def momentJsonRecord009 : SourceJson :=
  (momentRecordsChunk009Push []).head (List.cons_ne_nil _ _)

theorem moment_record_009_push_eq (acc : List SourceJson) :
    momentRecordsChunk009Push acc = momentJsonRecord009 :: acc := by rfl

noncomputable def momentTypedRecord009 : MomentRecord :=
  { simplexId := 9,
    factorFloorsQ80 := #[(317184247603283219167 : Int), (345744041093710549204 : Int), (135351489553280839044 : Int), (352165884912418332532 : Int), (308528602283156030021 : Int), (291416083002897834881 : Int), (741655139807991358403 : Int), (453722795136774182340 : Int), (465043721920108055329 : Int), (371056640484826819276 : Int)],
    oldFloorQ96 := (12771772851490484 : Int),
    newFloorQ96 := (12811789199297245 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_009_before_decode"
  err.flush

theorem decode_moment_record_009 :
    decodeMomentRecord momentJsonRecord009 = .ok momentTypedRecord009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_009_decoded"
  err.flush

noncomputable def momentJsonRecord010 : SourceJson :=
  (momentRecordsChunk010Push []).head (List.cons_ne_nil _ _)

theorem moment_record_010_push_eq (acc : List SourceJson) :
    momentRecordsChunk010Push acc = momentJsonRecord010 :: acc := by rfl

noncomputable def momentTypedRecord010 : MomentRecord :=
  { simplexId := 10,
    factorFloorsQ80 := #[(315177730533389944729 : Int), (332136959237660933407 : Int), (134127928832177461723 : Int), (361048449049392002769 : Int), (313624900770703459958 : Int), (291813186404671969795 : Int), (739928103873205513132 : Int), (461412940581808176468 : Int), (461028066096885729447 : Int), (375317918137298379630 : Int)],
    oldFloorQ96 := (16794721805152316 : Int),
    newFloorQ96 := (16847395027791347 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_010_before_decode"
  err.flush

theorem decode_moment_record_010 :
    decodeMomentRecord momentJsonRecord010 = .ok momentTypedRecord010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_010_decoded"
  err.flush

noncomputable def momentJsonRecord011 : SourceJson :=
  (momentRecordsChunk011Push []).head (List.cons_ne_nil _ _)

theorem moment_record_011_push_eq (acc : List SourceJson) :
    momentRecordsChunk011Push acc = momentJsonRecord011 :: acc := by rfl

noncomputable def momentTypedRecord011 : MomentRecord :=
  { simplexId := 11,
    factorFloorsQ80 := #[(321550562266642166684 : Int), (347375680643058872393 : Int), (131760879348096122724 : Int), (415437785745507207418 : Int), (329609987386016409376 : Int), (297485618292821704558 : Int), (740195019945610051852 : Int), (528131343657604261663 : Int), (577697409385331045060 : Int), (538158634102567031873 : Int)],
    oldFloorQ96 := (2356904742433 : Int),
    newFloorQ96 := (2365160854262 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_011_before_decode"
  err.flush

theorem decode_moment_record_011 :
    decodeMomentRecord momentJsonRecord011 = .ok momentTypedRecord011 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_011_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock002 : List SourceJson := [momentJsonRecord008, momentJsonRecord009, momentJsonRecord010, momentJsonRecord011]
noncomputable def momentTypedRecordsBlock002 : List MomentRecord := [momentTypedRecord008, momentTypedRecord009, momentTypedRecord010, momentTypedRecord011]

theorem moment_records_block_002_push_eq (acc : List SourceJson) :
    momentRecordsBlock002Push acc = [momentJsonRecord011, momentJsonRecord010, momentJsonRecord009, momentJsonRecord008] ++ acc := by rfl

theorem moment_records_block_002_reverse (acc : List SourceJson) :
    (momentRecordsBlock002Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock002 := by
  rw [moment_records_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_002 :
    momentJsonRecordsBlock002.mapM decodeMomentRecord = .ok momentTypedRecordsBlock002 := by
  simp only [momentJsonRecordsBlock002, momentTypedRecordsBlock002, List.mapM_cons, List.mapM_nil,
    decode_moment_record_008, decode_moment_record_009, decode_moment_record_010, decode_moment_record_011]
  rfl

noncomputable def momentTypedRowsThroughBlock002 : List MomentRecord := momentTypedRowsThroughBlock001 ++ momentTypedRecordsBlock002

theorem decode_moment_records_through_block_002 :
    momentRecordsAcc012.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock002 := by
  change (momentRecordsBlock002Push momentRecordsAcc008).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_002_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_001, decode_moment_records_block_002]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_block_002_complete"
  err.flush

#print axioms moment_record_008_push_eq
#print axioms decode_moment_record_008
#print axioms moment_record_009_push_eq
#print axioms decode_moment_record_009
#print axioms moment_record_010_push_eq
#print axioms decode_moment_record_010
#print axioms moment_record_011_push_eq
#print axioms decode_moment_record_011
#print axioms moment_records_block_002_push_eq
#print axioms moment_records_block_002_reverse
#print axioms decode_moment_records_block_002
#print axioms decode_moment_records_through_block_002

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
