import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock002
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock003

/-! Original typed moment records 12 through 15; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord012 : SourceJson :=
  (momentRecordsChunk012Push []).head (List.cons_ne_nil _ _)

theorem moment_record_012_push_eq (acc : List SourceJson) :
    momentRecordsChunk012Push acc = momentJsonRecord012 :: acc := by rfl

noncomputable def momentTypedRecord012 : MomentRecord :=
  { simplexId := 12,
    factorFloorsQ80 := #[(327299115345353557041 : Int), (348539546989704901287 : Int), (131760879348096122724 : Int), (357469102637204684762 : Int), (329609987386016409376 : Int), (297485618292821704558 : Int), (740195019945610051852 : Int), (528131343657604261663 : Int), (479889811306883597286 : Int), (370114727602666618682 : Int)],
    oldFloorQ96 := (24605554774822340 : Int),
    newFloorQ96 := (24685274877973366 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_012_before_decode"
  err.flush

theorem decode_moment_record_012 :
    decodeMomentRecord momentJsonRecord012 = .ok momentTypedRecord012 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_012_decoded"
  err.flush

noncomputable def momentJsonRecord013 : SourceJson :=
  (momentRecordsChunk013Push []).head (List.cons_ne_nil _ _)

theorem moment_record_013_push_eq (acc : List SourceJson) :
    momentRecordsChunk013Push acc = momentJsonRecord013 :: acc := by rfl

noncomputable def momentTypedRecord013 : MomentRecord :=
  { simplexId := 13,
    factorFloorsQ80 := #[(359402031222969823790 : Int), (386162937684017079029 : Int), (173586228264272683908 : Int), (396925120386652022543 : Int), (353436458161723692572 : Int), (396041358785107496701 : Int), (1271898816642884564965 : Int), (383036185520180280523 : Int), (454458877414571663518 : Int), (215562918068530604216 : Int)],
    oldFloorQ96 := (1694941296182 : Int),
    newFloorQ96 := (1701108082955 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_013_before_decode"
  err.flush

theorem decode_moment_record_013 :
    decodeMomentRecord momentJsonRecord013 = .ok momentTypedRecord013 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_013_decoded"
  err.flush

noncomputable def momentJsonRecord014 : SourceJson :=
  (momentRecordsChunk014Push []).head (List.cons_ne_nil _ _)

theorem moment_record_014_push_eq (acc : List SourceJson) :
    momentRecordsChunk014Push acc = momentJsonRecord014 :: acc := by rfl

noncomputable def momentTypedRecord014 : MomentRecord :=
  { simplexId := 14,
    factorFloorsQ80 := #[(433832875624794980929 : Int), (453473938379548229676 : Int), (166294909342567435848 : Int), (415966010684333576452 : Int), (364121204141486830915 : Int), (376123436236508631794 : Int), (948773924216782327113 : Int), (351191986551373498004 : Int), (460556479462063139305 : Int), (258393093264633052863 : Int)],
    oldFloorQ96 := (1686608461146 : Int),
    newFloorQ96 := (1692518415724 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_014_before_decode"
  err.flush

theorem decode_moment_record_014 :
    decodeMomentRecord momentJsonRecord014 = .ok momentTypedRecord014 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_014_decoded"
  err.flush

noncomputable def momentJsonRecord015 : SourceJson :=
  (momentRecordsChunk015Push []).head (List.cons_ne_nil _ _)

theorem moment_record_015_push_eq (acc : List SourceJson) :
    momentRecordsChunk015Push acc = momentJsonRecord015 :: acc := by rfl

noncomputable def momentTypedRecord015 : MomentRecord :=
  { simplexId := 15,
    factorFloorsQ80 := #[(358117294039540806707 : Int), (392014290997473223024 : Int), (164369513640561877458 : Int), (354838189988464003029 : Int), (355606250233818597226 : Int), (342035300415172811623 : Int), (880098472568970590106 : Int), (349964737432885951455 : Int), (457741674743890650073 : Int), (215918444410257391969 : Int)],
    oldFloorQ96 := (8998538893334187 : Int),
    newFloorQ96 := (9027396330978642 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_015_before_decode"
  err.flush

theorem decode_moment_record_015 :
    decodeMomentRecord momentJsonRecord015 = .ok momentTypedRecord015 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_015_decoded"
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
  err.putStrLn "P26_MOMENT05 typed_block_003_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
