import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock031
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock032

/-! Original typed moment records 128 through 131; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord128 : SourceJson :=
  (momentRecordsChunk128Push []).head (List.cons_ne_nil _ _)

theorem moment_record_128_push_eq (acc : List SourceJson) :
    momentRecordsChunk128Push acc = momentJsonRecord128 :: acc := by rfl

noncomputable def momentTypedRecord128 : MomentRecord :=
  { simplexId := 128,
    factorFloorsQ80 := #[(2103233432596218125809 : Int), (2069733592342336189507 : Int), (249963531564241312861 : Int), (1000091243491049499441 : Int), (1193259935017478057247 : Int), (2546856743327874494335 : Int), (1777448744212317356156 : Int), (1610595318449379145167 : Int), (1449803632899337981242 : Int), (1449859135584159026928 : Int)],
    oldFloorQ96 := (310514249165 : Int),
    newFloorQ96 := (314508288379 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_128_before_decode"
  err.flush

theorem decode_moment_record_128 :
    decodeMomentRecord momentJsonRecord128 = .ok momentTypedRecord128 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_128_decoded"
  err.flush

noncomputable def momentJsonRecord129 : SourceJson :=
  (momentRecordsChunk129Push []).head (List.cons_ne_nil _ _)

theorem moment_record_129_push_eq (acc : List SourceJson) :
    momentRecordsChunk129Push acc = momentJsonRecord129 :: acc := by rfl

noncomputable def momentTypedRecord129 : MomentRecord :=
  { simplexId := 129,
    factorFloorsQ80 := #[(1511767643079211874463 : Int), (1497371220164820273237 : Int), (169369625869338674079 : Int), (924953112908861588866 : Int), (1211436913121814605448 : Int), (1877730345012697145141 : Int), (1540908253109893524498 : Int), (1406192186669931825082 : Int), (1280709874287572673328 : Int), (1280766860906455847551 : Int)],
    oldFloorQ96 := (39000239746 : Int),
    newFloorQ96 := (39412143691 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_129_before_decode"
  err.flush

theorem decode_moment_record_129 :
    decodeMomentRecord momentJsonRecord129 = .ok momentTypedRecord129 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_129_decoded"
  err.flush

noncomputable def momentJsonRecord130 : SourceJson :=
  (momentRecordsChunk130Push []).head (List.cons_ne_nil _ _)

theorem moment_record_130_push_eq (acc : List SourceJson) :
    momentRecordsChunk130Push acc = momentJsonRecord130 :: acc := by rfl

noncomputable def momentTypedRecord130 : MomentRecord :=
  { simplexId := 130,
    factorFloorsQ80 := #[(608599884744395913018 : Int), (646543713133628521887 : Int), (388708076152566874298 : Int), (684151269587618042657 : Int), (1218611567197394136297 : Int), (3020796066618760279918 : Int), (2236287795775690923720 : Int), (1110088019433256212492 : Int), (888004203042519686537 : Int), (888031059573958974667 : Int)],
    oldFloorQ96 := (986585320861711 : Int),
    newFloorQ96 := (996171472244431 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_130_before_decode"
  err.flush

theorem decode_moment_record_130 :
    decodeMomentRecord momentJsonRecord130 = .ok momentTypedRecord130 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_130_decoded"
  err.flush

noncomputable def momentJsonRecord131 : SourceJson :=
  (momentRecordsChunk131Push []).head (List.cons_ne_nil _ _)

theorem moment_record_131_push_eq (acc : List SourceJson) :
    momentRecordsChunk131Push acc = momentJsonRecord131 :: acc := by rfl

noncomputable def momentTypedRecord131 : MomentRecord :=
  { simplexId := 131,
    factorFloorsQ80 := #[(1017522480918695784116 : Int), (1082613968765891161139 : Int), (377792897837313217542 : Int), (770865498389209856771 : Int), (1292695882450426251790 : Int), (2919690118921645309827 : Int), (1644264639140141807167 : Int), (1303946474860345988893 : Int), (1314401604837110335657 : Int), (1314437050077392324600 : Int)],
    oldFloorQ96 := (207143529617525 : Int),
    newFloorQ96 := (209389657021152 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_131_before_decode"
  err.flush

theorem decode_moment_record_131 :
    decodeMomentRecord momentJsonRecord131 = .ok momentTypedRecord131 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_131_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock032 : List SourceJson := [momentJsonRecord128, momentJsonRecord129, momentJsonRecord130, momentJsonRecord131]
noncomputable def momentTypedRecordsBlock032 : List MomentRecord := [momentTypedRecord128, momentTypedRecord129, momentTypedRecord130, momentTypedRecord131]

theorem moment_records_block_032_push_eq (acc : List SourceJson) :
    momentRecordsBlock032Push acc = [momentJsonRecord131, momentJsonRecord130, momentJsonRecord129, momentJsonRecord128] ++ acc := by rfl

theorem moment_records_block_032_reverse (acc : List SourceJson) :
    (momentRecordsBlock032Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock032 := by
  rw [moment_records_block_032_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_032 :
    momentJsonRecordsBlock032.mapM decodeMomentRecord = .ok momentTypedRecordsBlock032 := by
  simp only [momentJsonRecordsBlock032, momentTypedRecordsBlock032, List.mapM_cons, List.mapM_nil,
    decode_moment_record_128, decode_moment_record_129, decode_moment_record_130, decode_moment_record_131]
  rfl

noncomputable def momentTypedRowsThroughBlock032 : List MomentRecord := momentTypedRowsThroughBlock031 ++ momentTypedRecordsBlock032

theorem decode_moment_records_through_block_032 :
    momentRecordsAcc132.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock032 := by
  change (momentRecordsBlock032Push momentRecordsAcc128).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_032_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_031, decode_moment_records_block_032]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_032_complete"
  err.flush

#print axioms moment_record_128_push_eq
#print axioms decode_moment_record_128
#print axioms moment_record_129_push_eq
#print axioms decode_moment_record_129
#print axioms moment_record_130_push_eq
#print axioms decode_moment_record_130
#print axioms moment_record_131_push_eq
#print axioms decode_moment_record_131
#print axioms moment_records_block_032_push_eq
#print axioms moment_records_block_032_reverse
#print axioms decode_moment_records_block_032
#print axioms decode_moment_records_through_block_032

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
