import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock013
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock014

/-! Original typed moment records 56 through 59; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord056 : SourceJson :=
  (momentRecordsChunk056Push []).head (List.cons_ne_nil _ _)

theorem moment_record_056_push_eq (acc : List SourceJson) :
    momentRecordsChunk056Push acc = momentJsonRecord056 :: acc := by rfl

noncomputable def momentTypedRecord056 : MomentRecord :=
  { simplexId := 56,
    factorFloorsQ80 := #[(2117993800364727071667 : Int), (2291340930577847734952 : Int), (256915714803066210377 : Int), (549842992347631291561 : Int), (1025517765136520879777 : Int), (1716652362644357372963 : Int), (1481946182041418899978 : Int), (991596834110024775910 : Int), (991574129855369967406 : Int), (1986466520341882806407 : Int)],
    oldFloorQ96 := (349867224932593 : Int),
    newFloorQ96 := (353769683635880 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_056_before_decode"
  err.flush

theorem decode_moment_record_056 :
    decodeMomentRecord momentJsonRecord056 = .ok momentTypedRecord056 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_056_decoded"
  err.flush

noncomputable def momentJsonRecord057 : SourceJson :=
  (momentRecordsChunk057Push []).head (List.cons_ne_nil _ _)

theorem moment_record_057_push_eq (acc : List SourceJson) :
    momentRecordsChunk057Push acc = momentJsonRecord057 :: acc := by rfl

noncomputable def momentTypedRecord057 : MomentRecord :=
  { simplexId := 57,
    factorFloorsQ80 := #[(2047756475502320685600 : Int), (2004693160746407188326 : Int), (205461772872438258567 : Int), (590648720223893356126 : Int), (1087631798003030425569 : Int), (1718867636114597119472 : Int), (1265855213680672555438 : Int), (936510243032859331796 : Int), (936497491630810636840 : Int), (1855526631355529066390 : Int)],
    oldFloorQ96 := (10803325738343 : Int),
    newFloorQ96 := (10916958480103 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_057_before_decode"
  err.flush

theorem decode_moment_record_057 :
    decodeMomentRecord momentJsonRecord057 = .ok momentTypedRecord057 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_057_decoded"
  err.flush

noncomputable def momentJsonRecord058 : SourceJson :=
  (momentRecordsChunk058Push []).head (List.cons_ne_nil _ _)

theorem moment_record_058_push_eq (acc : List SourceJson) :
    momentRecordsChunk058Push acc = momentJsonRecord058 :: acc := by rfl

noncomputable def momentTypedRecord058 : MomentRecord :=
  { simplexId := 58,
    factorFloorsQ80 := #[(1935029284202914186708 : Int), (1899921310004045070457 : Int), (191841219731554035584 : Int), (641524427834526930587 : Int), (1146569410882959092958 : Int), (1726306728346233953148 : Int), (1241516845626811183313 : Int), (962659098874045281867 : Int), (962649451356601062456 : Int), (1574921467577575287700 : Int)],
    oldFloorQ96 := (3611927298092 : Int),
    newFloorQ96 := (3648812295831 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_058_before_decode"
  err.flush

theorem decode_moment_record_058 :
    decodeMomentRecord momentJsonRecord058 = .ok momentTypedRecord058 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_058_decoded"
  err.flush

noncomputable def momentJsonRecord059 : SourceJson :=
  (momentRecordsChunk059Push []).head (List.cons_ne_nil _ _)

theorem moment_record_059_push_eq (acc : List SourceJson) :
    momentRecordsChunk059Push acc = momentJsonRecord059 :: acc := by rfl

noncomputable def momentTypedRecord059 : MomentRecord :=
  { simplexId := 59,
    factorFloorsQ80 := #[(1011981599855880343511 : Int), (994171464460938060588 : Int), (139950010334858742466 : Int), (595964893605075872871 : Int), (1110115662668898195261 : Int), (1314439771481901892737 : Int), (964540630380435617070 : Int), (754610079293130287625 : Int), (754604621095913384723 : Int), (1458359228514800657545 : Int)],
    oldFloorQ96 := (451909521304 : Int),
    newFloorQ96 := (455323559131 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_059_before_decode"
  err.flush

theorem decode_moment_record_059 :
    decodeMomentRecord momentJsonRecord059 = .ok momentTypedRecord059 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_059_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock014 : List SourceJson := [momentJsonRecord056, momentJsonRecord057, momentJsonRecord058, momentJsonRecord059]
noncomputable def momentTypedRecordsBlock014 : List MomentRecord := [momentTypedRecord056, momentTypedRecord057, momentTypedRecord058, momentTypedRecord059]

theorem moment_records_block_014_push_eq (acc : List SourceJson) :
    momentRecordsBlock014Push acc = [momentJsonRecord059, momentJsonRecord058, momentJsonRecord057, momentJsonRecord056] ++ acc := by rfl

theorem moment_records_block_014_reverse (acc : List SourceJson) :
    (momentRecordsBlock014Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock014 := by
  rw [moment_records_block_014_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_014 :
    momentJsonRecordsBlock014.mapM decodeMomentRecord = .ok momentTypedRecordsBlock014 := by
  simp only [momentJsonRecordsBlock014, momentTypedRecordsBlock014, List.mapM_cons, List.mapM_nil,
    decode_moment_record_056, decode_moment_record_057, decode_moment_record_058, decode_moment_record_059]
  rfl

noncomputable def momentTypedRowsThroughBlock014 : List MomentRecord := momentTypedRowsThroughBlock013 ++ momentTypedRecordsBlock014

theorem decode_moment_records_through_block_014 :
    momentRecordsAcc060.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock014 := by
  change (momentRecordsBlock014Push momentRecordsAcc056).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_014_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_013, decode_moment_records_block_014]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_014_complete"
  err.flush

#print axioms moment_record_056_push_eq
#print axioms decode_moment_record_056
#print axioms moment_record_057_push_eq
#print axioms decode_moment_record_057
#print axioms moment_record_058_push_eq
#print axioms decode_moment_record_058
#print axioms moment_record_059_push_eq
#print axioms decode_moment_record_059
#print axioms moment_records_block_014_push_eq
#print axioms moment_records_block_014_reverse
#print axioms decode_moment_records_block_014
#print axioms decode_moment_records_through_block_014

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
