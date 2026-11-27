import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock003
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock004

/-! Original typed moment records 16 through 19; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord016 : SourceJson :=
  (momentRecordsChunk016Push []).head (List.cons_ne_nil _ _)

theorem moment_record_016_push_eq (acc : List SourceJson) :
    momentRecordsChunk016Push acc = momentJsonRecord016 :: acc := by rfl

noncomputable def momentTypedRecord016 : MomentRecord :=
  { simplexId := 16,
    factorFloorsQ80 := #[(355668912188113337083 : Int), (376291004282177856972 : Int), (162688754528200385576 : Int), (373137831767917756995 : Int), (363354661840826715144 : Int), (344704663787593750877 : Int), (876468461185077294831 : Int), (367162931343951167848 : Int), (497896247280056597958 : Int), (207542487066058106647 : Int)],
    oldFloorQ96 := (11827620728481054 : Int),
    newFloorQ96 := (11866082854074030 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_016_before_decode"
  err.flush

theorem decode_moment_record_016 :
    decodeMomentRecord momentJsonRecord016 = .ok momentTypedRecord016 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_016_decoded"
  err.flush

noncomputable def momentJsonRecord017 : SourceJson :=
  (momentRecordsChunk017Push []).head (List.cons_ne_nil _ _)

theorem moment_record_017_push_eq (acc : List SourceJson) :
    momentRecordsChunk017Push acc = momentJsonRecord017 :: acc := by rfl

noncomputable def momentTypedRecord017 : MomentRecord :=
  { simplexId := 17,
    factorFloorsQ80 := #[(370562695175819572377 : Int), (395255555456893149710 : Int), (159248870754103905661 : Int), (371454984120957869656 : Int), (385450740544817112148 : Int), (355758648373820821161 : Int), (872354795928323634506 : Int), (456806236327581630223 : Int), (445869488975288648202 : Int), (217622717441449295752 : Int)],
    oldFloorQ96 := (17332424431975888 : Int),
    newFloorQ96 := (17390304669603523 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_017_before_decode"
  err.flush

theorem decode_moment_record_017 :
    decodeMomentRecord momentJsonRecord017 = .ok momentTypedRecord017 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_017_decoded"
  err.flush

noncomputable def momentJsonRecord018 : SourceJson :=
  (momentRecordsChunk018Push []).head (List.cons_ne_nil _ _)

theorem moment_record_018_push_eq (acc : List SourceJson) :
    momentRecordsChunk018Push acc = momentJsonRecord018 :: acc := by rfl

noncomputable def momentTypedRecord018 : MomentRecord :=
  { simplexId := 18,
    factorFloorsQ80 := #[(363497064677335650185 : Int), (390981581701111631837 : Int), (187920506630209275443 : Int), (429420531443317085421 : Int), (389300100989940083952 : Int), (425515551741978939705 : Int), (1683005046326196376257 : Int), (282819224661166304500 : Int), (222762825919307689303 : Int), (222779686865786802657 : Int)],
    oldFloorQ96 := (1129148525899 : Int),
    newFloorQ96 := (1133451282108 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_018_before_decode"
  err.flush

theorem decode_moment_record_018 :
    decodeMomentRecord momentJsonRecord018 = .ok momentTypedRecord018 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_018_decoded"
  err.flush

noncomputable def momentJsonRecord019 : SourceJson :=
  (momentRecordsChunk019Push []).head (List.cons_ne_nil _ _)

theorem moment_record_019_push_eq (acc : List SourceJson) :
    momentRecordsChunk019Push acc = momentJsonRecord019 :: acc := by rfl

noncomputable def momentTypedRecord019 : MomentRecord :=
  { simplexId := 19,
    factorFloorsQ80 := #[(439419246645198240408 : Int), (459742730445812571241 : Int), (179458964511682993459 : Int), (450515074191043208121 : Int), (404363272057545522460 : Int), (401908916559139342108 : Int), (1253409772047187332888 : Int), (282420885667897148476 : Int), (266900831914899190512 : Int), (266905668959633520815 : Int)],
    oldFloorQ96 := (1124038590562 : Int),
    newFloorQ96 := (1128141797566 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_019_before_decode"
  err.flush

theorem decode_moment_record_019 :
    decodeMomentRecord momentJsonRecord019 = .ok momentTypedRecord019 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_019_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock004 : List SourceJson := [momentJsonRecord016, momentJsonRecord017, momentJsonRecord018, momentJsonRecord019]
noncomputable def momentTypedRecordsBlock004 : List MomentRecord := [momentTypedRecord016, momentTypedRecord017, momentTypedRecord018, momentTypedRecord019]

theorem moment_records_block_004_push_eq (acc : List SourceJson) :
    momentRecordsBlock004Push acc = [momentJsonRecord019, momentJsonRecord018, momentJsonRecord017, momentJsonRecord016] ++ acc := by rfl

theorem moment_records_block_004_reverse (acc : List SourceJson) :
    (momentRecordsBlock004Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock004 := by
  rw [moment_records_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_004 :
    momentJsonRecordsBlock004.mapM decodeMomentRecord = .ok momentTypedRecordsBlock004 := by
  simp only [momentJsonRecordsBlock004, momentTypedRecordsBlock004, List.mapM_cons, List.mapM_nil,
    decode_moment_record_016, decode_moment_record_017, decode_moment_record_018, decode_moment_record_019]
  rfl

noncomputable def momentTypedRowsThroughBlock004 : List MomentRecord := momentTypedRowsThroughBlock003 ++ momentTypedRecordsBlock004

theorem decode_moment_records_through_block_004 :
    momentRecordsAcc020.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock004 := by
  change (momentRecordsBlock004Push momentRecordsAcc016).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_004_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_003, decode_moment_records_block_004]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_block_004_complete"
  err.flush

#print axioms moment_record_016_push_eq
#print axioms decode_moment_record_016
#print axioms moment_record_017_push_eq
#print axioms decode_moment_record_017
#print axioms moment_record_018_push_eq
#print axioms decode_moment_record_018
#print axioms moment_record_019_push_eq
#print axioms decode_moment_record_019
#print axioms moment_records_block_004_push_eq
#print axioms moment_records_block_004_reverse
#print axioms decode_moment_records_block_004
#print axioms decode_moment_records_through_block_004

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
