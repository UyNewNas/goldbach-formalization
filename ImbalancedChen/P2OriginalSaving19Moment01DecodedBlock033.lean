import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock032
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock033

/-! Original typed moment records 132 through 135; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord132 : SourceJson :=
  (momentRecordsChunk132Push []).head (List.cons_ne_nil _ _)

theorem moment_record_132_push_eq (acc : List SourceJson) :
    momentRecordsChunk132Push acc = momentJsonRecord132 :: acc := by rfl

noncomputable def momentTypedRecord132 : MomentRecord :=
  { simplexId := 132,
    factorFloorsQ80 := #[(1376738776105050530828 : Int), (1472909584761725462660 : Int), (365910285299357391931 : Int), (861301111359118312870 : Int), (1349728617860946771332 : Int), (2788833527416912837040 : Int), (1827165310453894968919 : Int), (1516091330453557836518 : Int), (1549117618403826623642 : Int), (1549160086744974588019 : Int)],
    oldFloorQ96 := (45006440435030 : Int),
    newFloorQ96 := (45555417390427 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_132_before_decode"
  err.flush

theorem decode_moment_record_132 :
    decodeMomentRecord momentJsonRecord132 = .ok momentTypedRecord132 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_132_decoded"
  err.flush

noncomputable def momentJsonRecord133 : SourceJson :=
  (momentRecordsChunk133Push []).head (List.cons_ne_nil _ _)

theorem moment_record_133_push_eq (acc : List SourceJson) :
    momentRecordsChunk133Push acc = momentJsonRecord133 :: acc := by rfl

noncomputable def momentTypedRecord133 : MomentRecord :=
  { simplexId := 133,
    factorFloorsQ80 := #[(1778115477845878243266 : Int), (1903778300252426578848 : Int), (346455204043563750396 : Int), (945519663179992742886 : Int), (1398800904605758381293 : Int), (2783980148867094663221 : Int), (2034370427437304379084 : Int), (1767443442677857007306 : Int), (1768194571505359713619 : Int), (1768243324043592261391 : Int)],
    oldFloorQ96 := (10281309171671 : Int),
    newFloorQ96 := (10422551422079 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_133_before_decode"
  err.flush

theorem decode_moment_record_133 :
    decodeMomentRecord momentJsonRecord133 = .ok momentTypedRecord133 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_133_decoded"
  err.flush

noncomputable def momentJsonRecord134 : SourceJson :=
  (momentRecordsChunk134Push []).head (List.cons_ne_nil _ _)

theorem moment_record_134_push_eq (acc : List SourceJson) :
    momentRecordsChunk134Push acc = momentJsonRecord134 :: acc := by rfl

noncomputable def momentTypedRecord134 : MomentRecord :=
  { simplexId := 134,
    factorFloorsQ80 := #[(1926032523104238704184 : Int), (1878653133285476505335 : Int), (269885769508710799061 : Int), (1090755419779499953869 : Int), (1111504584914923465192 : Int), (2811689941152700685987 : Int), (1950500952565038135428 : Int), (1768123762860729166964 : Int), (1590146506871807829806 : Int), (1590201368345367372971 : Int)],
    oldFloorQ96 := (279839765250 : Int),
    newFloorQ96 := (283565097094 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_134_before_decode"
  err.flush

theorem decode_moment_record_134 :
    decodeMomentRecord momentJsonRecord134 = .ok momentTypedRecord134 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_134_decoded"
  err.flush

noncomputable def momentJsonRecord135 : SourceJson :=
  (momentRecordsChunk135Push []).head (List.cons_ne_nil _ _)

theorem moment_record_135_push_eq (acc : List SourceJson) :
    momentRecordsChunk135Push acc = momentJsonRecord135 :: acc := by rfl

noncomputable def momentTypedRecord135 : MomentRecord :=
  { simplexId := 135,
    factorFloorsQ80 := #[(1489556409392539313960 : Int), (1453034318080416632076 : Int), (186147983467702000911 : Int), (1033157275619464545382 : Int), (942159622371538433819 : Int), (2099538491992705894672 : Int), (1751227078024742313375 : Int), (1612022698212734890282 : Int), (1481540606375038041612 : Int), (1481597701604640937844 : Int)],
    oldFloorQ96 := (56895940758 : Int),
    newFloorQ96 := (57536281819 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_135_before_decode"
  err.flush

theorem decode_moment_record_135 :
    decodeMomentRecord momentJsonRecord135 = .ok momentTypedRecord135 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_135_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock033 : List SourceJson := [momentJsonRecord132, momentJsonRecord133, momentJsonRecord134, momentJsonRecord135]
noncomputable def momentTypedRecordsBlock033 : List MomentRecord := [momentTypedRecord132, momentTypedRecord133, momentTypedRecord134, momentTypedRecord135]

theorem moment_records_block_033_push_eq (acc : List SourceJson) :
    momentRecordsBlock033Push acc = [momentJsonRecord135, momentJsonRecord134, momentJsonRecord133, momentJsonRecord132] ++ acc := by rfl

theorem moment_records_block_033_reverse (acc : List SourceJson) :
    (momentRecordsBlock033Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock033 := by
  rw [moment_records_block_033_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_033 :
    momentJsonRecordsBlock033.mapM decodeMomentRecord = .ok momentTypedRecordsBlock033 := by
  simp only [momentJsonRecordsBlock033, momentTypedRecordsBlock033, List.mapM_cons, List.mapM_nil,
    decode_moment_record_132, decode_moment_record_133, decode_moment_record_134, decode_moment_record_135]
  rfl

noncomputable def momentTypedRowsThroughBlock033 : List MomentRecord := momentTypedRowsThroughBlock032 ++ momentTypedRecordsBlock033

theorem decode_moment_records_through_block_033 :
    momentRecordsAcc136.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock033 := by
  change (momentRecordsBlock033Push momentRecordsAcc132).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_033_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_032, decode_moment_records_block_033]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_033_complete"
  err.flush

#print axioms moment_record_132_push_eq
#print axioms decode_moment_record_132
#print axioms moment_record_133_push_eq
#print axioms decode_moment_record_133
#print axioms moment_record_134_push_eq
#print axioms decode_moment_record_134
#print axioms moment_record_135_push_eq
#print axioms decode_moment_record_135
#print axioms moment_records_block_033_push_eq
#print axioms moment_records_block_033_reverse
#print axioms decode_moment_records_block_033
#print axioms decode_moment_records_through_block_033

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
