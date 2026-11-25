import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock026
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock027

/-! Original typed moment records 108 through 111; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord108 : SourceJson :=
  (momentRecordsChunk108Push []).head (List.cons_ne_nil _ _)

theorem moment_record_108_push_eq (acc : List SourceJson) :
    momentRecordsChunk108Push acc = momentJsonRecord108 :: acc := by rfl

noncomputable def momentTypedRecord108 : MomentRecord :=
  { simplexId := 108,
    factorFloorsQ80 := #[(1110315894637888625243 : Int), (1152066937665140464135 : Int), (337619754507348733220 : Int), (635601972696645950864 : Int), (2147727981775208253880 : Int), (2493427309362525207949 : Int), (1372460159891038856965 : Int), (1052458455891503931922 : Int), (1160092339140135592151 : Int), (1160136352262066059468 : Int)],
    oldFloorQ96 := (199001277445954 : Int),
    newFloorQ96 := (201089853485022 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_108_before_decode"
  err.flush

theorem decode_moment_record_108 :
    decodeMomentRecord momentJsonRecord108 = .ok momentTypedRecord108 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_108_decoded"
  err.flush

noncomputable def momentJsonRecord109 : SourceJson :=
  (momentRecordsChunk109Push []).head (List.cons_ne_nil _ _)

theorem moment_record_109_push_eq (acc : List SourceJson) :
    momentRecordsChunk109Push acc = momentJsonRecord109 :: acc := by rfl

noncomputable def momentTypedRecord109 : MomentRecord :=
  { simplexId := 109,
    factorFloorsQ80 := #[(1514428613725893382946 : Int), (1584314386943208376864 : Int), (327087371203760011861 : Int), (716270231399115480780 : Int), (2178491350495018644038 : Int), (2372074338288839764113 : Int), (1540124386846046409069 : Int), (1248018615014282869368 : Int), (1337142165397788392170 : Int), (1337201202759958234458 : Int)],
    oldFloorQ96 := (43275512554206 : Int),
    newFloorQ96 := (43785197874052 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_109_before_decode"
  err.flush

theorem decode_moment_record_109 :
    decodeMomentRecord momentJsonRecord109 = .ok momentTypedRecord109 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_109_decoded"
  err.flush

noncomputable def momentJsonRecord110 : SourceJson :=
  (momentRecordsChunk110Push []).head (List.cons_ne_nil _ _)

theorem moment_record_110_push_eq (acc : List SourceJson) :
    momentRecordsChunk110Push acc = momentJsonRecord110 :: acc := by rfl

noncomputable def momentTypedRecord110 : MomentRecord :=
  { simplexId := 110,
    factorFloorsQ80 := #[(1988550658404774403376 : Int), (2083038630738066571595 : Int), (309452233407187031196 : Int), (791738358624742952356 : Int), (2167176758179863670359 : Int), (2367927685283853577518 : Int), (1725250757719559000603 : Int), (1475283505036452898215 : Int), (1504081903428454267743 : Int), (1504154533711697270775 : Int)],
    oldFloorQ96 := (9897098327832 : Int),
    newFloorQ96 := (10028264571193 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_110_before_decode"
  err.flush

theorem decode_moment_record_110 :
    decodeMomentRecord momentJsonRecord110 = .ok momentTypedRecord110 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_110_decoded"
  err.flush

noncomputable def momentJsonRecord111 : SourceJson :=
  (momentRecordsChunk111Push []).head (List.cons_ne_nil _ _)

theorem moment_record_111_push_eq (acc : List SourceJson) :
    momentRecordsChunk111Push acc = momentJsonRecord111 :: acc := by rfl

noncomputable def momentTypedRecord111 : MomentRecord :=
  { simplexId := 111,
    factorFloorsQ80 := #[(2273449152847912194287 : Int), (2221287583859020578915 : Int), (236970222668147493767 : Int), (909389131754845251160 : Int), (1674962864946135354976 : Int), (2393427251682790667617 : Int), (1605327999008079146387 : Int), (1436116596444760505275 : Int), (1272861574245842060836 : Int), (1272948024610289563704 : Int)],
    oldFloorQ96 := (270082838186 : Int),
    newFloorQ96 := (273521953144 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_111_before_decode"
  err.flush

theorem decode_moment_record_111 :
    decodeMomentRecord momentJsonRecord111 = .ok momentTypedRecord111 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_111_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock027 : List SourceJson := [momentJsonRecord108, momentJsonRecord109, momentJsonRecord110, momentJsonRecord111]
noncomputable def momentTypedRecordsBlock027 : List MomentRecord := [momentTypedRecord108, momentTypedRecord109, momentTypedRecord110, momentTypedRecord111]

theorem moment_records_block_027_push_eq (acc : List SourceJson) :
    momentRecordsBlock027Push acc = [momentJsonRecord111, momentJsonRecord110, momentJsonRecord109, momentJsonRecord108] ++ acc := by rfl

theorem moment_records_block_027_reverse (acc : List SourceJson) :
    (momentRecordsBlock027Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock027 := by
  rw [moment_records_block_027_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_027 :
    momentJsonRecordsBlock027.mapM decodeMomentRecord = .ok momentTypedRecordsBlock027 := by
  simp only [momentJsonRecordsBlock027, momentTypedRecordsBlock027, List.mapM_cons, List.mapM_nil,
    decode_moment_record_108, decode_moment_record_109, decode_moment_record_110, decode_moment_record_111]
  rfl

noncomputable def momentTypedRowsThroughBlock027 : List MomentRecord := momentTypedRowsThroughBlock026 ++ momentTypedRecordsBlock027

theorem decode_moment_records_through_block_027 :
    momentRecordsAcc112.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock027 := by
  change (momentRecordsBlock027Push momentRecordsAcc108).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_027_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_026, decode_moment_records_block_027]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_027_complete"
  err.flush

#print axioms moment_record_108_push_eq
#print axioms decode_moment_record_108
#print axioms moment_record_109_push_eq
#print axioms decode_moment_record_109
#print axioms moment_record_110_push_eq
#print axioms decode_moment_record_110
#print axioms moment_record_111_push_eq
#print axioms decode_moment_record_111
#print axioms moment_records_block_027_push_eq
#print axioms moment_records_block_027_reverse
#print axioms decode_moment_records_block_027
#print axioms decode_moment_records_through_block_027

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
