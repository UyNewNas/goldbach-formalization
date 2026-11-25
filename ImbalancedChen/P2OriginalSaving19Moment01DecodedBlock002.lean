import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock001
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock002

/-! Original typed moment records 8 through 11; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord008 : SourceJson :=
  (momentRecordsChunk008Push []).head (List.cons_ne_nil _ _)

theorem moment_record_008_push_eq (acc : List SourceJson) :
    momentRecordsChunk008Push acc = momentJsonRecord008 :: acc := by rfl

noncomputable def momentTypedRecord008 : MomentRecord :=
  { simplexId := 8,
    factorFloorsQ80 := #[(1375312016583850034293 : Int), (1466316095306043925592 : Int), (263704637088221092635 : Int), (385060923425073489692 : Int), (601676750241805014331 : Int), (1660522128118673496756 : Int), (749832888505194487627 : Int), (767633556040481306459 : Int), (1079353443464234653761 : Int), (721879665085597039154 : Int)],
    oldFloorQ96 := (7073030839087679012 : Int),
    newFloorQ96 := (7126303629670592339 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_008_before_decode"
  err.flush

theorem decode_moment_record_008 :
    decodeMomentRecord momentJsonRecord008 = .ok momentTypedRecord008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_008_decoded"
  err.flush

noncomputable def momentJsonRecord009 : SourceJson :=
  (momentRecordsChunk009Push []).head (List.cons_ne_nil _ _)

theorem moment_record_009_push_eq (acc : List SourceJson) :
    momentRecordsChunk009Push acc = momentJsonRecord009 :: acc := by rfl

noncomputable def momentTypedRecord009 : MomentRecord :=
  { simplexId := 9,
    factorFloorsQ80 := #[(1334839870277527453999 : Int), (1452331069136883221646 : Int), (245379705728981786236 : Int), (332605955593618982060 : Int), (573492412643415721753 : Int), (1745678773146748101319 : Int), (934980098502993478514 : Int), (689673502758291086031 : Int), (955050482813262271173 : Int), (816192630730140979981 : Int)],
    oldFloorQ96 := (8506162335173161194 : Int),
    newFloorQ96 := (8570292536432318113 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_009_before_decode"
  err.flush

theorem decode_moment_record_009 :
    decodeMomentRecord momentJsonRecord009 = .ok momentTypedRecord009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_009_decoded"
  err.flush

noncomputable def momentJsonRecord010 : SourceJson :=
  (momentRecordsChunk010Push []).head (List.cons_ne_nil _ _)

theorem moment_record_010_push_eq (acc : List SourceJson) :
    momentRecordsChunk010Push acc = momentJsonRecord010 :: acc := by rfl

noncomputable def momentTypedRecord010 : MomentRecord :=
  { simplexId := 10,
    factorFloorsQ80 := #[(1065787647074943391372 : Int), (1247644231407436921503 : Int), (208659658533008851828 : Int), (161636573672861010697 : Int), (486358744839744688639 : Int), (1100300955792572699807 : Int), (947485476900419725763 : Int), (687276052904635674454 : Int), (938457496882311937079 : Int), (730948510547541069587 : Int)],
    oldFloorQ96 := (3718202562367335390 : Int),
    newFloorQ96 := (3741572189521011558 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_010_before_decode"
  err.flush

theorem decode_moment_record_010 :
    decodeMomentRecord momentJsonRecord010 = .ok momentTypedRecord010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_010_decoded"
  err.flush

noncomputable def momentJsonRecord011 : SourceJson :=
  (momentRecordsChunk011Push []).head (List.cons_ne_nil _ _)

theorem moment_record_011_push_eq (acc : List SourceJson) :
    momentRecordsChunk011Push acc = momentJsonRecord011 :: acc := by rfl

noncomputable def momentTypedRecord011 : MomentRecord :=
  { simplexId := 11,
    factorFloorsQ80 := #[(1338121271762846751127 : Int), (1454304660270774073676 : Int), (255122904111609870596 : Int), (352450118552439271369 : Int), (507330400371331069173 : Int), (1677482205800745471837 : Int), (730038320924358899477 : Int), (661831061309642780298 : Int), (1094024020809845589579 : Int), (812766671233321818380 : Int)],
    oldFloorQ96 := (5706333873279710728 : Int),
    newFloorQ96 := (5748419797045749543 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_011_before_decode"
  err.flush

theorem decode_moment_record_011 :
    decodeMomentRecord momentJsonRecord011 = .ok momentTypedRecord011 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_011_decoded"
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
  err.putStrLn "P26_MOMENT01 typed_block_002_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
