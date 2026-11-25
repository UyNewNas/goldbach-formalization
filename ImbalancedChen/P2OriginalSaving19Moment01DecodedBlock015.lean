import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock014
import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock015

/-! Original typed moment records 60 through 63; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

noncomputable def momentJsonRecord060 : SourceJson :=
  (momentRecordsChunk060Push []).head (List.cons_ne_nil _ _)

theorem moment_record_060_push_eq (acc : List SourceJson) :
    momentRecordsChunk060Push acc = momentJsonRecord060 :: acc := by rfl

noncomputable def momentTypedRecord060 : MomentRecord :=
  { simplexId := 60,
    factorFloorsQ80 := #[(2359040746482009383250 : Int), (2534723807839490739481 : Int), (263664088666943268745 : Int), (336617533620758255657 : Int), (644982207516273072608 : Int), (1916562969033580114749 : Int), (946400527720171883934 : Int), (785847418931336007307 : Int), (1010930847114366403765 : Int), (1010905722389458699449 : Int)],
    oldFloorQ96 := (599686697449891 : Int),
    newFloorQ96 := (605573584510325 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_060_before_decode"
  err.flush

theorem decode_moment_record_060 :
    decodeMomentRecord momentJsonRecord060 = .ok momentTypedRecord060 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_060_decoded"
  err.flush

noncomputable def momentJsonRecord061 : SourceJson :=
  (momentRecordsChunk061Push []).head (List.cons_ne_nil _ _)

theorem moment_record_061_push_eq (acc : List SourceJson) :
    momentRecordsChunk061Push acc = momentJsonRecord061 :: acc := by rfl

noncomputable def momentTypedRecord061 : MomentRecord :=
  { simplexId := 61,
    factorFloorsQ80 := #[(2042127403494031837928 : Int), (2299294085754063157287 : Int), (217862596334724529858 : Int), (165617497644349710714 : Int), (541883901940168692589 : Int), (1211609322910159212788 : Int), (957446489816795882115 : Int), (784251803373139570529 : Int), (989593899312199947874 : Int), (989562522253970880912 : Int)],
    oldFloorQ96 := (315338869987728 : Int),
    newFloorQ96 := (318010518598992 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_061_before_decode"
  err.flush

theorem decode_moment_record_061 :
    decodeMomentRecord momentJsonRecord061 = .ok momentTypedRecord061 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_061_decoded"
  err.flush

noncomputable def momentJsonRecord062 : SourceJson :=
  (momentRecordsChunk062Push []).head (List.cons_ne_nil _ _)

theorem moment_record_062_push_eq (acc : List SourceJson) :
    momentRecordsChunk062Push acc = momentJsonRecord062 :: acc := by rfl

noncomputable def momentTypedRecord062 : MomentRecord :=
  { simplexId := 62,
    factorFloorsQ80 := #[(2434929987330492865952 : Int), (2595991074923897466598 : Int), (272392893369222486279 : Int), (364326900979200541318 : Int), (637914707551456374586 : Int), (1836656638262434668012 : Int), (727435360320207640179 : Int), (751466906309959446421 : Int), (967601721219417630255 : Int), (967579667082206791488 : Int)],
    oldFloorQ96 := (462362175850439 : Int),
    newFloorQ96 := (466803154416073 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_062_before_decode"
  err.flush

theorem decode_moment_record_062 :
    decodeMomentRecord momentJsonRecord062 = .ok momentTypedRecord062 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_062_decoded"
  err.flush

noncomputable def momentJsonRecord063 : SourceJson :=
  (momentRecordsChunk063Push []).head (List.cons_ne_nil _ _)

theorem moment_record_063_push_eq (acc : List SourceJson) :
    momentRecordsChunk063Push acc = momentJsonRecord063 :: acc := by rfl

noncomputable def momentTypedRecord063 : MomentRecord :=
  { simplexId := 63,
    factorFloorsQ80 := #[(2461653188969278442318 : Int), (2611542908622618743825 : Int), (282069828873389804580 : Int), (381476017305468544881 : Int), (830660470420274552651 : Int), (1936851246880743543656 : Int), (784005187615036367769 : Int), (923029089724554796374 : Int), (906092114855771277296 : Int), (906072369228235051349 : Int)],
    oldFloorQ96 := (666118499766877 : Int),
    newFloorQ96 := (672776479301422 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_063_before_decode"
  err.flush

theorem decode_moment_record_063 :
    decodeMomentRecord momentJsonRecord063 = .ok momentTypedRecord063 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_record_063_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock015 : List SourceJson := [momentJsonRecord060, momentJsonRecord061, momentJsonRecord062, momentJsonRecord063]
noncomputable def momentTypedRecordsBlock015 : List MomentRecord := [momentTypedRecord060, momentTypedRecord061, momentTypedRecord062, momentTypedRecord063]

theorem moment_records_block_015_push_eq (acc : List SourceJson) :
    momentRecordsBlock015Push acc = [momentJsonRecord063, momentJsonRecord062, momentJsonRecord061, momentJsonRecord060] ++ acc := by rfl

theorem moment_records_block_015_reverse (acc : List SourceJson) :
    (momentRecordsBlock015Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock015 := by
  rw [moment_records_block_015_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_015 :
    momentJsonRecordsBlock015.mapM decodeMomentRecord = .ok momentTypedRecordsBlock015 := by
  simp only [momentJsonRecordsBlock015, momentTypedRecordsBlock015, List.mapM_cons, List.mapM_nil,
    decode_moment_record_060, decode_moment_record_061, decode_moment_record_062, decode_moment_record_063]
  rfl

noncomputable def momentTypedRowsThroughBlock015 : List MomentRecord := momentTypedRowsThroughBlock014 ++ momentTypedRecordsBlock015

theorem decode_moment_records_through_block_015 :
    momentRecordsAcc064.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock015 := by
  change (momentRecordsBlock015Push momentRecordsAcc060).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_015_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_014, decode_moment_records_block_015]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_block_015_complete"
  err.flush

#print axioms moment_record_060_push_eq
#print axioms decode_moment_record_060
#print axioms moment_record_061_push_eq
#print axioms decode_moment_record_061
#print axioms moment_record_062_push_eq
#print axioms decode_moment_record_062
#print axioms moment_record_063_push_eq
#print axioms decode_moment_record_063
#print axioms moment_records_block_015_push_eq
#print axioms moment_records_block_015_reverse
#print axioms decode_moment_records_block_015
#print axioms decode_moment_records_through_block_015

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
