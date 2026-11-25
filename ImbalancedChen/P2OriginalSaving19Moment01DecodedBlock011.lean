import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock010
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock011

/-! Original typed moment records 44 through 47; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord044 : SourceJson :=
  (momentRecordsChunk044Push []).head (List.cons_ne_nil _ _)

theorem moment_record_044_push_eq (acc : List SourceJson) :
    momentRecordsChunk044Push acc = momentJsonRecord044 :: acc := by rfl

noncomputable def momentTypedRecord044 : MomentRecord :=
  { simplexId := 44,
    factorFloorsQ80 := #[(2639748176033667784102 : Int), (2599597284886125769068 : Int), (229469091795960437224 : Int), (681303743592285329498 : Int), (1239224894255121667667 : Int), (2016414106395994744633 : Int), (1427628801926136267814 : Int), (1273236071073736949970 : Int), (1126291007510741719654 : Int), (1126390876445211840975 : Int)],
    oldFloorQ96 := (279257019130 : Int),
    newFloorQ96 := (282593737692 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_044_before_decode"
  err.flush

theorem decode_moment_record_044 :
    decodeMomentRecord momentJsonRecord044 = .ok momentTypedRecord044 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_044_decoded"
  err.flush

noncomputable def momentJsonRecord045 : SourceJson :=
  (momentRecordsChunk045Push []).head (List.cons_ne_nil _ _)

theorem moment_record_045_push_eq (acc : List SourceJson) :
    momentRecordsChunk045Push acc = momentJsonRecord045 :: acc := by rfl

noncomputable def momentTypedRecord045 : MomentRecord :=
  { simplexId := 45,
    factorFloorsQ80 := #[(1938644189159209912412 : Int), (1912386975436962090512 : Int), (178288710244763371079 : Int), (681303743592285329498 : Int), (1238576542564998773039 : Int), (1644168797953332526037 : Int), (1192470867909457294364 : Int), (1077424128691721692853 : Int), (973490737314416772879 : Int), (973586422339260041983 : Int)],
    oldFloorQ96 := (285076391113 : Int),
    newFloorQ96 := (287875031674 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_045_before_decode"
  err.flush

theorem decode_moment_record_045 :
    decodeMomentRecord momentJsonRecord045 = .ok momentTypedRecord045 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_045_decoded"
  err.flush

noncomputable def momentJsonRecord046 : SourceJson :=
  (momentRecordsChunk046Push []).head (List.cons_ne_nil _ _)

theorem moment_record_046_push_eq (acc : List SourceJson) :
    momentRecordsChunk046Push acc = momentJsonRecord046 :: acc := by rfl

noncomputable def momentTypedRecord046 : MomentRecord :=
  { simplexId := 46,
    factorFloorsQ80 := #[(2384913149213166771207 : Int), (2624842979307747749007 : Int), (236091364860379789909 : Int), (642454371316787535353 : Int), (1263289099170609520451 : Int), (1617077411257047223303 : Int), (1525402931529020674227 : Int), (1345715105284030457744 : Int), (1185037069002905378946 : Int), (1507339485382290397268 : Int)],
    oldFloorQ96 := (11871196947144054 : Int),
    newFloorQ96 := (12012770930275357 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_046_before_decode"
  err.flush

theorem decode_moment_record_046 :
    decodeMomentRecord momentJsonRecord046 = .ok momentTypedRecord046 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_046_decoded"
  err.flush

noncomputable def momentJsonRecord047 : SourceJson :=
  (momentRecordsChunk047Push []).head (List.cons_ne_nil _ _)

theorem moment_record_047_push_eq (acc : List SourceJson) :
    momentRecordsChunk047Push acc = momentJsonRecord047 :: acc := by rfl

noncomputable def momentTypedRecord047 : MomentRecord :=
  { simplexId := 47,
    factorFloorsQ80 := #[(1960673148804749194515 : Int), (1919938933341125655607 : Int), (177849738621290551130 : Int), (657971573098416793833 : Int), (1229194811283664955641 : Int), (1631039646189452448225 : Int), (1190714998165388532850 : Int), (1075126389334065320989 : Int), (977371986229075820317 : Int), (957484982882734899052 : Int)],
    oldFloorQ96 := (683731317951866 : Int),
    newFloorQ96 := (690424785316870 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_047_before_decode"
  err.flush

theorem decode_moment_record_047 :
    decodeMomentRecord momentJsonRecord047 = .ok momentTypedRecord047 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_047_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock011 : List SourceJson := [momentJsonRecord044, momentJsonRecord045, momentJsonRecord046, momentJsonRecord047]
noncomputable def momentTypedRecordsBlock011 : List MomentRecord := [momentTypedRecord044, momentTypedRecord045, momentTypedRecord046, momentTypedRecord047]

theorem moment_records_block_011_push_eq (acc : List SourceJson) :
    momentRecordsBlock011Push acc = [momentJsonRecord047, momentJsonRecord046, momentJsonRecord045, momentJsonRecord044] ++ acc := by rfl

theorem moment_records_block_011_reverse (acc : List SourceJson) :
    (momentRecordsBlock011Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock011 := by
  rw [moment_records_block_011_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_011 :
    momentJsonRecordsBlock011.mapM decodeMomentRecord = .ok momentTypedRecordsBlock011 := by
  simp only [momentJsonRecordsBlock011, momentTypedRecordsBlock011, List.mapM_cons, List.mapM_nil,
    decode_moment_record_044, decode_moment_record_045, decode_moment_record_046, decode_moment_record_047]
  rfl

noncomputable def momentTypedRowsThroughBlock011 : List MomentRecord := momentTypedRowsThroughBlock010 ++ momentTypedRecordsBlock011

theorem decode_moment_records_through_block_011 :
    momentRecordsAcc048.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock011 := by
  change (momentRecordsBlock011Push momentRecordsAcc044).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_011_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_010, decode_moment_records_block_011]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_011_complete"
  err.flush

#print axioms moment_record_044_push_eq
#print axioms decode_moment_record_044
#print axioms moment_record_045_push_eq
#print axioms decode_moment_record_045
#print axioms moment_record_046_push_eq
#print axioms decode_moment_record_046
#print axioms moment_record_047_push_eq
#print axioms decode_moment_record_047
#print axioms moment_records_block_011_push_eq
#print axioms moment_records_block_011_reverse
#print axioms decode_moment_records_block_011
#print axioms decode_moment_records_through_block_011

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
