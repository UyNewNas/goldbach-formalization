/- SOURCE_CANDIDATE: original Cell06 source only. No Lean compilation,
independent kernel replay, full-owned audit or formal acceptance is claimed. -/

import ImbalancedChen.P2OriginalSaving19Moment06DecodedBlock002
import ImbalancedChen.P2OriginalSaving19Moment06RecordsBlock003

/-! Original typed moment records 12 through 15; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment06Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment06Parsing

noncomputable def momentJsonRecord012 : SourceJson :=
  (momentRecordsChunk012Push []).head (List.cons_ne_nil _ _)

theorem moment_record_012_push_eq (acc : List SourceJson) :
    momentRecordsChunk012Push acc = momentJsonRecord012 :: acc := by rfl

noncomputable def momentTypedRecord012 : MomentRecord :=
  { simplexId := 12,
    factorFloorsQ80 := #[(391618429484089455103 : Int), (358699033322558920519 : Int), (141164920291027981216 : Int), (247220148178497615405 : Int), (285976759546553897029 : Int), (261586849158223429811 : Int), (797038368897278830567 : Int), (445427627429362014525 : Int), (539853976421130027671 : Int), (485143874586243712358 : Int)],
    oldFloorQ96 := (698370846384202426 : Int),
    newFloorQ96 := (700658571376970879 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_012_before_decode"
  err.flush

theorem decode_moment_record_012 :
    decodeMomentRecord momentJsonRecord012 = .ok momentTypedRecord012 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_012_decoded"
  err.flush

noncomputable def momentJsonRecord013 : SourceJson :=
  (momentRecordsChunk013Push []).head (List.cons_ne_nil _ _)

theorem moment_record_013_push_eq (acc : List SourceJson) :
    momentRecordsChunk013Push acc = momentJsonRecord013 :: acc := by rfl

noncomputable def momentTypedRecord013 : MomentRecord :=
  { simplexId := 13,
    factorFloorsQ80 := #[(288386835425169427035 : Int), (290193313096367331678 : Int), (141350524724598595828 : Int), (248077157594864530576 : Int), (292845480174355755103 : Int), (237506131484376521635 : Int), (805792642402958063104 : Int), (346623696152243764843 : Int), (352084805100061117440 : Int), (287654634419280021395 : Int)],
    oldFloorQ96 := (227869297626324260 : Int),
    newFloorQ96 := (228490368611452803 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_013_before_decode"
  err.flush

theorem decode_moment_record_013 :
    decodeMomentRecord momentJsonRecord013 = .ok momentTypedRecord013 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_013_decoded"
  err.flush

noncomputable def momentJsonRecord014 : SourceJson :=
  (momentRecordsChunk014Push []).head (List.cons_ne_nil _ _)

theorem moment_record_014_push_eq (acc : List SourceJson) :
    momentRecordsChunk014Push acc = momentJsonRecord014 :: acc := by rfl

noncomputable def momentTypedRecord014 : MomentRecord :=
  { simplexId := 14,
    factorFloorsQ80 := #[(330050115260754958800 : Int), (272925724791446017062 : Int), (162517628617356356071 : Int), (246108756400033588959 : Int), (305697336981067626386 : Int), (162869972569846336607 : Int), (154760669240028721404 : Int), (160151811037228145887 : Int), (203908168077369068737 : Int), (324953346205722309242 : Int)],
    oldFloorQ96 := (12533951323478439 : Int),
    newFloorQ96 := (12558068775029953 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_014_before_decode"
  err.flush

theorem decode_moment_record_014 :
    decodeMomentRecord momentJsonRecord014 = .ok momentTypedRecord014 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_014_decoded"
  err.flush

noncomputable def momentJsonRecord015 : SourceJson :=
  (momentRecordsChunk015Push []).head (List.cons_ne_nil _ _)

theorem moment_record_015_push_eq (acc : List SourceJson) :
    momentRecordsChunk015Push acc = momentJsonRecord015 :: acc := by rfl

noncomputable def momentTypedRecord015 : MomentRecord :=
  { simplexId := 15,
    factorFloorsQ80 := #[(329688667897747805364 : Int), (272904345034751501053 : Int), (149662850764813556126 : Int), (255034438899054673751 : Int), (303778070655059198774 : Int), (197976758940998599660 : Int), (764195489427564824424 : Int), (277580345615883622179 : Int), (301269015066775547264 : Int), (326133874183266268345 : Int)],
    oldFloorQ96 := (98980536398036791 : Int),
    newFloorQ96 := (99241095129038454 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_015_before_decode"
  err.flush

theorem decode_moment_record_015 :
    decodeMomentRecord momentJsonRecord015 = .ok momentTypedRecord015 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_record_015_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock003 : List SourceJson := [momentJsonRecord012, momentJsonRecord013, momentJsonRecord014, momentJsonRecord015]
noncomputable def momentTypedRecordsBlock003 : List MomentRecord := [momentTypedRecord012, momentTypedRecord013, momentTypedRecord014, momentTypedRecord015]

theorem moment_records_block_003_push_eq (acc : List SourceJson) :
    momentRecordsBlock003Push acc = [momentJsonRecord015, momentJsonRecord014, momentJsonRecord013, momentJsonRecord012] ++ acc := by rfl

theorem moment_records_block_003_reverse (acc : List SourceJson) :
    (momentRecordsBlock003Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock003 := by
  rw [moment_records_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_003 :
    momentJsonRecordsBlock003.mapM decodeMomentRecord = .ok momentTypedRecordsBlock003 := by
  simp only [momentJsonRecordsBlock003, momentTypedRecordsBlock003, List.mapM_cons, List.mapM_nil,
    decode_moment_record_012, decode_moment_record_013, decode_moment_record_014, decode_moment_record_015]
  rfl

noncomputable def momentTypedRowsThroughBlock003 : List MomentRecord := momentTypedRowsThroughBlock002 ++ momentTypedRecordsBlock003

theorem decode_moment_records_through_block_003 :
    momentRecordsAcc016.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock003 := by
  change (momentRecordsBlock003Push momentRecordsAcc012).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_003_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_002, decode_moment_records_block_003]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 typed_block_003_complete"
  err.flush

#print axioms moment_record_012_push_eq
#print axioms decode_moment_record_012
#print axioms moment_record_013_push_eq
#print axioms decode_moment_record_013
#print axioms moment_record_014_push_eq
#print axioms decode_moment_record_014
#print axioms moment_record_015_push_eq
#print axioms decode_moment_record_015
#print axioms moment_records_block_003_push_eq
#print axioms moment_records_block_003_reverse
#print axioms decode_moment_records_block_003
#print axioms decode_moment_records_through_block_003

end ImbalancedChen.P2OriginalSaving19Moment06Decoding
