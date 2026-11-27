import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock009
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock010

/-! Original typed moment records 40 through 43; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord040 : SourceJson :=
  (momentRecordsChunk040Push []).head (List.cons_ne_nil _ _)

theorem moment_record_040_push_eq (acc : List SourceJson) :
    momentRecordsChunk040Push acc = momentJsonRecord040 :: acc := by rfl

noncomputable def momentTypedRecord040 : MomentRecord :=
  { simplexId := 40,
    factorFloorsQ80 := #[(286896452535860319345 : Int), (338057031676764764876 : Int), (159552078340988809890 : Int), (311788640715698424224 : Int), (337938627834066087668 : Int), (328496147971883600211 : Int), (1270716267408330595911 : Int), (243885020341862533507 : Int), (335895376961963737566 : Int), (268560927095687491448 : Int)],
    oldFloorQ96 := (11811246091317022 : Int),
    newFloorQ96 := (11849232230119463 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_040_before_decode"
  err.flush

theorem decode_moment_record_040 :
    decodeMomentRecord momentJsonRecord040 = .ok momentTypedRecord040 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_040_decoded"
  err.flush

noncomputable def momentJsonRecord041 : SourceJson :=
  (momentRecordsChunk041Push []).head (List.cons_ne_nil _ _)

theorem moment_record_041_push_eq (acc : List SourceJson) :
    momentRecordsChunk041Push acc = momentJsonRecord041 :: acc := by rfl

noncomputable def momentTypedRecord041 : MomentRecord :=
  { simplexId := 41,
    factorFloorsQ80 := #[(258573143488345767136 : Int), (321433637441508642970 : Int), (139080714733208664475 : Int), (244127685766792569857 : Int), (286369525637344709437 : Int), (297360953215394171237 : Int), (1343704352432266001306 : Int), (291695562091264481643 : Int), (336220840050481922522 : Int), (290130315571044825091 : Int)],
    oldFloorQ96 := (11316834060977760 : Int),
    newFloorQ96 := (11352543743158269 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_041_before_decode"
  err.flush

theorem decode_moment_record_041 :
    decodeMomentRecord momentJsonRecord041 = .ok momentTypedRecord041 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_041_decoded"
  err.flush

noncomputable def momentJsonRecord042 : SourceJson :=
  (momentRecordsChunk042Push []).head (List.cons_ne_nil _ _)

theorem moment_record_042_push_eq (acc : List SourceJson) :
    momentRecordsChunk042Push acc = momentJsonRecord042 :: acc := by rfl

noncomputable def momentTypedRecord042 : MomentRecord :=
  { simplexId := 42,
    factorFloorsQ80 := #[(203587634991216747466 : Int), (266593081098375657020 : Int), (83686866972559299633 : Int), (114300139197717748124 : Int), (195440424100349289021 : Int), (124930247861207793201 : Int), (651803067445735324234 : Int), (295553086071416545790 : Int), (329038632371068552629 : Int), (265551484114153569111 : Int)],
    oldFloorQ96 := (12560693798861384 : Int),
    newFloorQ96 := (12587012974959924 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_042_before_decode"
  err.flush

theorem decode_moment_record_042 :
    decodeMomentRecord momentJsonRecord042 = .ok momentTypedRecord042 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_042_decoded"
  err.flush

noncomputable def momentJsonRecord043 : SourceJson :=
  (momentRecordsChunk043Push []).head (List.cons_ne_nil _ _)

theorem moment_record_043_push_eq (acc : List SourceJson) :
    momentRecordsChunk043Push acc = momentJsonRecord043 :: acc := by rfl

noncomputable def momentTypedRecord043 : MomentRecord :=
  { simplexId := 43,
    factorFloorsQ80 := #[(484064619267624635405 : Int), (512688895709140466842 : Int), (171572738067385210430 : Int), (420471001191093178841 : Int), (429648446816196138789 : Int), (387192164672560668939 : Int), (914444939524792879843 : Int), (469624831993087338343 : Int), (325665506241183190126 : Int), (325700838275901023253 : Int)],
    oldFloorQ96 := (1886657710545 : Int),
    newFloorQ96 := (1893601226194 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_043_before_decode"
  err.flush

theorem decode_moment_record_043 :
    decodeMomentRecord momentJsonRecord043 = .ok momentTypedRecord043 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_043_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock010 : List SourceJson := [momentJsonRecord040, momentJsonRecord041, momentJsonRecord042, momentJsonRecord043]
noncomputable def momentTypedRecordsBlock010 : List MomentRecord := [momentTypedRecord040, momentTypedRecord041, momentTypedRecord042, momentTypedRecord043]

theorem moment_records_block_010_push_eq (acc : List SourceJson) :
    momentRecordsBlock010Push acc = [momentJsonRecord043, momentJsonRecord042, momentJsonRecord041, momentJsonRecord040] ++ acc := by rfl

theorem moment_records_block_010_reverse (acc : List SourceJson) :
    (momentRecordsBlock010Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock010 := by
  rw [moment_records_block_010_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_010 :
    momentJsonRecordsBlock010.mapM decodeMomentRecord = .ok momentTypedRecordsBlock010 := by
  simp only [momentJsonRecordsBlock010, momentTypedRecordsBlock010, List.mapM_cons, List.mapM_nil,
    decode_moment_record_040, decode_moment_record_041, decode_moment_record_042, decode_moment_record_043]
  rfl

noncomputable def momentTypedRowsThroughBlock010 : List MomentRecord := momentTypedRowsThroughBlock009 ++ momentTypedRecordsBlock010

theorem decode_moment_records_through_block_010 :
    momentRecordsAcc044.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock010 := by
  change (momentRecordsBlock010Push momentRecordsAcc040).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_010_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_009, decode_moment_records_block_010]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_block_010_complete"
  err.flush

#print axioms moment_record_040_push_eq
#print axioms decode_moment_record_040
#print axioms moment_record_041_push_eq
#print axioms decode_moment_record_041
#print axioms moment_record_042_push_eq
#print axioms decode_moment_record_042
#print axioms moment_record_043_push_eq
#print axioms decode_moment_record_043
#print axioms moment_records_block_010_push_eq
#print axioms moment_records_block_010_reverse
#print axioms decode_moment_records_block_010
#print axioms decode_moment_records_through_block_010

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
