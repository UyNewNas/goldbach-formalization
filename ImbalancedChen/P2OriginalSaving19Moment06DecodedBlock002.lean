/- SOURCE_CANDIDATE: original Cell06 source only. No Lean compilation,
independent kernel replay, full-owned audit or formal acceptance is claimed. -/

import ImbalancedChen.P2OriginalSaving19Moment06DecodedBlock001
import ImbalancedChen.P2OriginalSaving19Moment06RecordsBlock002

/-! Original typed moment records 8 through 11; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment06Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment06Parsing

noncomputable def momentJsonRecord008 : SourceJson :=
  (momentRecordsChunk008Push []).head (List.cons_ne_nil _ _)

theorem moment_record_008_push_eq (acc : List SourceJson) :
    momentRecordsChunk008Push acc = momentJsonRecord008 :: acc := by rfl

noncomputable def momentTypedRecord008 : MomentRecord :=
  { simplexId := 8,
    factorFloorsQ80 := #[(324276953189135215904 : Int), (277855417275102614797 : Int), (163149685582329227412 : Int), (252343154095653518963 : Int), (310992436843025505908 : Int), (207617376606452125171 : Int), (787068895558476147174 : Int), (262716104346935154177 : Int), (282938643679505553295 : Int), (316945711743206199350 : Int)],
    oldFloorQ96 := (42576836926041919 : Int),
    newFloorQ96 := (42689188420938077 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_008_before_decode"
  err.flush

theorem decode_moment_record_008 :
    decodeMomentRecord momentJsonRecord008 = .ok momentTypedRecord008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_008_decoded"
  err.flush

noncomputable def momentJsonRecord009 : SourceJson :=
  (momentRecordsChunk009Push []).head (List.cons_ne_nil _ _)

theorem moment_record_009_push_eq (acc : List SourceJson) :
    momentRecordsChunk009Push acc = momentJsonRecord009 :: acc := by rfl

noncomputable def momentTypedRecord009 : MomentRecord :=
  { simplexId := 9,
    factorFloorsQ80 := #[(329690775038144117991 : Int), (272904959267853525443 : Int), (150584245414222828559 : Int), (260296065520012933155 : Int), (308044635845052105794 : Int), (230517201768012522753 : Int), (1196975440579302461428 : Int), (356109514505201420292 : Int), (349372935888127319717 : Int), (326131161210267075215 : Int)],
    oldFloorQ96 := (9717501901324 : Int),
    newFloorQ96 := (9747938635958 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_009_before_decode"
  err.flush

theorem decode_moment_record_009 :
    decodeMomentRecord momentJsonRecord009 = .ok momentTypedRecord009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_009_decoded"
  err.flush

noncomputable def momentJsonRecord010 : SourceJson :=
  (momentRecordsChunk010Push []).head (List.cons_ne_nil _ _)

theorem moment_record_010_push_eq (acc : List SourceJson) :
    momentRecordsChunk010Push acc = momentJsonRecord010 :: acc := by rfl

noncomputable def momentTypedRecord010 : MomentRecord :=
  { simplexId := 10,
    factorFloorsQ80 := #[(391615819805928365462 : Int), (358697458633508732413 : Int), (141165070174508863979 : Int), (247219592565868914806 : Int), (285976319991206316957 : Int), (261587608885436998483 : Int), (1178764847248173808455 : Int), (509788006480344317295 : Int), (539834412666088362963 : Int), (485145875794327121852 : Int)],
    oldFloorQ96 := (47773487978102 : Int),
    newFloorQ96 := (47947672784626 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_010_before_decode"
  err.flush

theorem decode_moment_record_010 :
    decodeMomentRecord momentJsonRecord010 = .ok momentTypedRecord010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_010_decoded"
  err.flush

noncomputable def momentJsonRecord011 : SourceJson :=
  (momentRecordsChunk011Push []).head (List.cons_ne_nil _ _)

theorem moment_record_011_push_eq (acc : List SourceJson) :
    momentRecordsChunk011Push acc = momentJsonRecord011 :: acc := by rfl

noncomputable def momentTypedRecord011 : MomentRecord :=
  { simplexId := 11,
    factorFloorsQ80 := #[(320560394098004116880 : Int), (278808942371562515770 : Int), (149091981109090004104 : Int), (259183632805550841814 : Int), (306685038991009635659 : Int), (235026572266854826613 : Int), (802203350178335089800 : Int), (346600970006098992802 : Int), (352897840842553244117 : Int), (317437731178735556868 : Int)],
    oldFloorQ96 := (326633556061839201 : Int),
    newFloorQ96 := (327544942223105774 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_011_before_decode"
  err.flush

theorem decode_moment_record_011 :
    decodeMomentRecord momentJsonRecord011 = .ok momentTypedRecord011 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_011_decoded"
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
  err.putStrLn "P26_MOMENT06 typed_block_002_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment06Decoding
