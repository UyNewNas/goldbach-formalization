import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock022
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock023

/-! Original typed moment records 92 through 95; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord092 : SourceJson :=
  (momentRecordsChunk092Push []).head (List.cons_ne_nil _ _)

theorem moment_record_092_push_eq (acc : List SourceJson) :
    momentRecordsChunk092Push acc = momentJsonRecord092 :: acc := by rfl

noncomputable def momentTypedRecord092 : MomentRecord :=
  { simplexId := 92,
    factorFloorsQ80 := #[(1971979293116440890774 : Int), (1929428387831838733336 : Int), (204191223784228304167 : Int), (816550413655689988484 : Int), (1027284143917797500094 : Int), (1925663484523992403661 : Int), (1390195029071991240403 : Int), (1262252741409261494808 : Int), (1144199785135475027419 : Int), (1144311391687946684672 : Int)],
    oldFloorQ96 := (255609653469 : Int),
    newFloorQ96 := (258333834868 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_092_before_decode"
  err.flush

theorem decode_moment_record_092 :
    decodeMomentRecord momentJsonRecord092 = .ok momentTypedRecord092 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_092_decoded"
  err.flush

noncomputable def momentJsonRecord093 : SourceJson :=
  (momentRecordsChunk093Push []).head (List.cons_ne_nil _ _)

theorem moment_record_093_push_eq (acc : List SourceJson) :
    momentRecordsChunk093Push acc = momentJsonRecord093 :: acc := by rfl

noncomputable def momentTypedRecord093 : MomentRecord :=
  { simplexId := 93,
    factorFloorsQ80 := #[(2014679529659341520452 : Int), (2135010023767219840383 : Int), (265680773480436075394 : Int), (747862423211322739881 : Int), (1424761678357364868762 : Int), (1892791880135951058418 : Int), (1689656404637537053344 : Int), (1493906682869333098337 : Int), (1317156333505564360196 : Int), (1627116885367754065086 : Int)],
    oldFloorQ96 := (10718505836948850 : Int),
    newFloorQ96 := (10848813656242995 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_093_before_decode"
  err.flush

theorem decode_moment_record_093 :
    decodeMomentRecord momentJsonRecord093 = .ok momentTypedRecord093 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_093_decoded"
  err.flush

noncomputable def momentJsonRecord094 : SourceJson :=
  (momentRecordsChunk094Push []).head (List.cons_ne_nil _ _)

theorem moment_record_094_push_eq (acc : List SourceJson) :
    momentRecordsChunk094Push acc = momentJsonRecord094 :: acc := by rfl

noncomputable def momentTypedRecord094 : MomentRecord :=
  { simplexId := 94,
    factorFloorsQ80 := #[(2011209314750960975360 : Int), (1943453867001574241912 : Int), (203687288126536002849 : Int), (789607368196055631646 : Int), (1026340564328034528676 : Int), (1908891439022627428322 : Int), (1388131555731301080519 : Int), (1259622901509917604567 : Int), (1148596155763663982053 : Int), (1125836716255669808922 : Int)],
    oldFloorQ96 := (612920906212943 : Int),
    newFloorQ96 := (619447690618239 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_094_before_decode"
  err.flush

theorem decode_moment_record_094 :
    decodeMomentRecord momentJsonRecord094 = .ok momentTypedRecord094 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_094_decoded"
  err.flush

noncomputable def momentJsonRecord095 : SourceJson :=
  (momentRecordsChunk095Push []).head (List.cons_ne_nil _ _)

theorem moment_record_095_push_eq (acc : List SourceJson) :
    momentRecordsChunk095Push acc = momentJsonRecord095 :: acc := by rfl

noncomputable def momentTypedRecord095 : MomentRecord :=
  { simplexId := 95,
    factorFloorsQ80 := #[(1724569581127002876590 : Int), (1826762741136386917709 : Int), (280856350723258338855 : Int), (695969334024665694360 : Int), (1425236927936090085243 : Int), (1894034801944718081495 : Int), (1606561024447841674023 : Int), (1372365237861382535284 : Int), (1192152024114984458030 : Int), (1789974724263330548818 : Int)],
    oldFloorQ96 := (150451984230304964 : Int),
    newFloorQ96 := (152180314920346384 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_095_before_decode"
  err.flush

theorem decode_moment_record_095 :
    decodeMomentRecord momentJsonRecord095 = .ok momentTypedRecord095 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_095_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock023 : List SourceJson := [momentJsonRecord092, momentJsonRecord093, momentJsonRecord094, momentJsonRecord095]
noncomputable def momentTypedRecordsBlock023 : List MomentRecord := [momentTypedRecord092, momentTypedRecord093, momentTypedRecord094, momentTypedRecord095]

theorem moment_records_block_023_push_eq (acc : List SourceJson) :
    momentRecordsBlock023Push acc = [momentJsonRecord095, momentJsonRecord094, momentJsonRecord093, momentJsonRecord092] ++ acc := by rfl

theorem moment_records_block_023_reverse (acc : List SourceJson) :
    (momentRecordsBlock023Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock023 := by
  rw [moment_records_block_023_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_023 :
    momentJsonRecordsBlock023.mapM decodeMomentRecord = .ok momentTypedRecordsBlock023 := by
  simp only [momentJsonRecordsBlock023, momentTypedRecordsBlock023, List.mapM_cons, List.mapM_nil,
    decode_moment_record_092, decode_moment_record_093, decode_moment_record_094, decode_moment_record_095]
  rfl

noncomputable def momentTypedRowsThroughBlock023 : List MomentRecord := momentTypedRowsThroughBlock022 ++ momentTypedRecordsBlock023

theorem decode_moment_records_through_block_023 :
    momentRecordsAcc096.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock023 := by
  change (momentRecordsBlock023Push momentRecordsAcc092).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_023_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_022, decode_moment_records_block_023]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_023_complete"
  err.flush

#print axioms moment_record_092_push_eq
#print axioms decode_moment_record_092
#print axioms moment_record_093_push_eq
#print axioms decode_moment_record_093
#print axioms moment_record_094_push_eq
#print axioms decode_moment_record_094
#print axioms moment_record_095_push_eq
#print axioms decode_moment_record_095
#print axioms moment_records_block_023_push_eq
#print axioms moment_records_block_023_reverse
#print axioms decode_moment_records_block_023
#print axioms decode_moment_records_through_block_023

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
