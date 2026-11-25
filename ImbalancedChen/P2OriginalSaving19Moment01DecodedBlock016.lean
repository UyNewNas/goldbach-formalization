import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock015
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock016

/-! Original typed moment records 64 through 67; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord064 : SourceJson :=
  (momentRecordsChunk064Push []).head (List.cons_ne_nil _ _)

theorem moment_record_064_push_eq (acc : List SourceJson) :
    momentRecordsChunk064Push acc = momentJsonRecord064 :: acc := by rfl

noncomputable def momentTypedRecord064 : MomentRecord :=
  { simplexId := 64,
    factorFloorsQ80 := #[(2447035198939849164526 : Int), (2575517600761912671328 : Int), (289230294277788826108 : Int), (380240657928281700831 : Int), (933840763292631641313 : Int), (2027163052358118285348 : Int), (1535711847525224656001 : Int), (1075038722320931318588 : Int), (728334187184309453359 : Int), (728318804515429656618 : Int)],
    oldFloorQ96 := (749580888814757 : Int),
    newFloorQ96 := (757509689657145 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_064_before_decode"
  err.flush

theorem decode_moment_record_064 :
    decodeMomentRecord momentJsonRecord064 = .ok momentTypedRecord064 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_064_decoded"
  err.flush

noncomputable def momentJsonRecord065 : SourceJson :=
  (momentRecordsChunk065Push []).head (List.cons_ne_nil _ _)

theorem moment_record_065_push_eq (acc : List SourceJson) :
    momentRecordsChunk065Push acc = momentJsonRecord065 :: acc := by rfl

noncomputable def momentTypedRecord065 : MomentRecord :=
  { simplexId := 65,
    factorFloorsQ80 := #[(2710809238185597202345 : Int), (2858246123412759381829 : Int), (287596659413170838864 : Int), (436723016298013747270 : Int), (1098062537375741107258 : Int), (2020506700269528035653 : Int), (1676310732843850180778 : Int), (871164834789523460724 : Int), (994399108924001496327 : Int), (994409164062172954641 : Int)],
    oldFloorQ96 := (1025334531979421 : Int),
    newFloorQ96 := (1037233046203813 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_065_before_decode"
  err.flush

theorem decode_moment_record_065 :
    decodeMomentRecord momentJsonRecord065 = .ok momentTypedRecord065 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_065_decoded"
  err.flush

noncomputable def momentJsonRecord066 : SourceJson :=
  (momentRecordsChunk066Push []).head (List.cons_ne_nil _ _)

theorem moment_record_066_push_eq (acc : List SourceJson) :
    momentRecordsChunk066Push acc = momentJsonRecord066 :: acc := by rfl

noncomputable def momentTypedRecord066 : MomentRecord :=
  { simplexId := 66,
    factorFloorsQ80 := #[(2937300961750152703283 : Int), (3129623607882241470088 : Int), (280594674971938289528 : Int), (499441721791659477573 : Int), (1246818787664951320268 : Int), (1942476722716822497790 : Int), (1170697418966610794280 : Int), (893364007658195702406 : Int), (1210611778259908854377 : Int), (1210639168675880730981 : Int)],
    oldFloorQ96 := (217286237139613 : Int),
    newFloorQ96 := (219912009351641 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_066_before_decode"
  err.flush

theorem decode_moment_record_066 :
    decodeMomentRecord momentJsonRecord066 = .ok momentTypedRecord066 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_066_decoded"
  err.flush

noncomputable def momentJsonRecord067 : SourceJson :=
  (momentRecordsChunk067Push []).head (List.cons_ne_nil _ _)

theorem moment_record_067_push_eq (acc : List SourceJson) :
    momentRecordsChunk067Push acc = momentJsonRecord067 :: acc := by rfl

noncomputable def momentTypedRecord067 : MomentRecord :=
  { simplexId := 67,
    factorFloorsQ80 := #[(3075106046681852338856 : Int), (3318819060882828845793 : Int), (272506689070742641888 : Int), (563057119710992895476 : Int), (1374296233697642538591 : Int), (1842107150424521104154 : Int), (1306763877282492559116 : Int), (1054782127904973174642 : Int), (1266823349533918879396 : Int), (1266865360312872712566 : Int)],
    oldFloorQ96 := (47650505686685 : Int),
    newFloorQ96 := (48259037905065 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_067_before_decode"
  err.flush

theorem decode_moment_record_067 :
    decodeMomentRecord momentJsonRecord067 = .ok momentTypedRecord067 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_067_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock016 : List SourceJson := [momentJsonRecord064, momentJsonRecord065, momentJsonRecord066, momentJsonRecord067]
noncomputable def momentTypedRecordsBlock016 : List MomentRecord := [momentTypedRecord064, momentTypedRecord065, momentTypedRecord066, momentTypedRecord067]

theorem moment_records_block_016_push_eq (acc : List SourceJson) :
    momentRecordsBlock016Push acc = [momentJsonRecord067, momentJsonRecord066, momentJsonRecord065, momentJsonRecord064] ++ acc := by rfl

theorem moment_records_block_016_reverse (acc : List SourceJson) :
    (momentRecordsBlock016Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock016 := by
  rw [moment_records_block_016_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_016 :
    momentJsonRecordsBlock016.mapM decodeMomentRecord = .ok momentTypedRecordsBlock016 := by
  simp only [momentJsonRecordsBlock016, momentTypedRecordsBlock016, List.mapM_cons, List.mapM_nil,
    decode_moment_record_064, decode_moment_record_065, decode_moment_record_066, decode_moment_record_067]
  rfl

noncomputable def momentTypedRowsThroughBlock016 : List MomentRecord := momentTypedRowsThroughBlock015 ++ momentTypedRecordsBlock016

theorem decode_moment_records_through_block_016 :
    momentRecordsAcc068.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock016 := by
  change (momentRecordsBlock016Push momentRecordsAcc064).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_016_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_015, decode_moment_records_block_016]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_016_complete"
  err.flush

#print axioms moment_record_064_push_eq
#print axioms decode_moment_record_064
#print axioms moment_record_065_push_eq
#print axioms decode_moment_record_065
#print axioms moment_record_066_push_eq
#print axioms decode_moment_record_066
#print axioms moment_record_067_push_eq
#print axioms decode_moment_record_067
#print axioms moment_records_block_016_push_eq
#print axioms moment_records_block_016_reverse
#print axioms decode_moment_records_block_016
#print axioms decode_moment_records_through_block_016

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
