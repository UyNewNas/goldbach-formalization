import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock006
import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock007

/-! Original typed moment records 28 through 31; each concrete value is checked by original decodeMomentRecord.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentJsonRecord028 : SourceJson :=
  (momentRecordsChunk028Push []).head (List.cons_ne_nil _ _)

theorem moment_record_028_push_eq (acc : List SourceJson) :
    momentRecordsChunk028Push acc = momentJsonRecord028 :: acc := by rfl

noncomputable def momentTypedRecord028 : MomentRecord :=
  { simplexId := 28,
    factorFloorsQ80 := #[(182643863522155932728 : Int), (240510209157083045219 : Int), (82159795427237029093 : Int), (105402828572297227994 : Int), (206543110970746249645 : Int), (128182056924691867978 : Int), (768147063306539784310 : Int), (346651565881481083315 : Int), (341242330376253496670 : Int), (226948304743523571546 : Int)],
    oldFloorQ96 := (987860435604 : Int),
    newFloorQ96 := (990010565734 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_028_before_decode"
  err.flush

theorem decode_moment_record_028 :
    decodeMomentRecord momentJsonRecord028 = .ok momentTypedRecord028 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_028_decoded"
  err.flush

noncomputable def momentJsonRecord029 : SourceJson :=
  (momentRecordsChunk029Push []).head (List.cons_ne_nil _ _)

theorem moment_record_029_push_eq (acc : List SourceJson) :
    momentRecordsChunk029Push acc = momentJsonRecord029 :: acc := by rfl

noncomputable def momentTypedRecord029 : MomentRecord :=
  { simplexId := 29,
    factorFloorsQ80 := #[(233365197925720255462 : Int), (308890262933703289553 : Int), (116157572787187784757 : Int), (158721449979357279563 : Int), (293069384208742018245 : Int), (172067650960000579053 : Int), (692815461784672038141 : Int), (311975198796252515867 : Int), (325697645667171386547 : Int), (240501493180207751576 : Int)],
    oldFloorQ96 := (3462250586301469 : Int),
    newFloorQ96 := (3470431710699526 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_029_before_decode"
  err.flush

theorem decode_moment_record_029 :
    decodeMomentRecord momentJsonRecord029 = .ok momentTypedRecord029 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_029_decoded"
  err.flush

noncomputable def momentJsonRecord030 : SourceJson :=
  (momentRecordsChunk030Push []).head (List.cons_ne_nil _ _)

theorem moment_record_030_push_eq (acc : List SourceJson) :
    momentRecordsChunk030Push acc = momentJsonRecord030 :: acc := by rfl

noncomputable def momentTypedRecord030 : MomentRecord :=
  { simplexId := 30,
    factorFloorsQ80 := #[(161889186759882804443 : Int), (213694107669416364035 : Int), (77437523312780878551 : Int), (97524543247928374024 : Int), (181045213757293825895 : Int), (118262518400306024235 : Int), (613595944247399759981 : Int), (257413972088776709169 : Int), (287676148592345317027 : Int), (185278381462200708945 : Int)],
    oldFloorQ96 := (2900799339714008 : Int),
    newFloorQ96 := (2906068151102325 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_030_before_decode"
  err.flush

theorem decode_moment_record_030 :
    decodeMomentRecord momentJsonRecord030 = .ok momentTypedRecord030 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_030_decoded"
  err.flush

noncomputable def momentJsonRecord031 : SourceJson :=
  (momentRecordsChunk031Push []).head (List.cons_ne_nil _ _)

theorem moment_record_031_push_eq (acc : List SourceJson) :
    momentRecordsChunk031Push acc = momentJsonRecord031 :: acc := by rfl

noncomputable def momentTypedRecord031 : MomentRecord :=
  { simplexId := 31,
    factorFloorsQ80 := #[(230885328507480250707 : Int), (276787632522820749474 : Int), (156841733169817949078 : Int), (289655414708173886511 : Int), (344441429036431810135 : Int), (339617045984478767915 : Int), (1245088130197833200610 : Int), (237713357740069536493 : Int), (365453226858081913012 : Int), (190657329423205689477 : Int)],
    oldFloorQ96 := (4673097776496284 : Int),
    newFloorQ96 := (4687333387397469 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_031_before_decode"
  err.flush

theorem decode_moment_record_031 :
    decodeMomentRecord momentJsonRecord031 = .ok momentTypedRecord031 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_record_031_decoded"
  err.flush

noncomputable def momentJsonRecordsBlock007 : List SourceJson := [momentJsonRecord028, momentJsonRecord029, momentJsonRecord030, momentJsonRecord031]
noncomputable def momentTypedRecordsBlock007 : List MomentRecord := [momentTypedRecord028, momentTypedRecord029, momentTypedRecord030, momentTypedRecord031]

theorem moment_records_block_007_push_eq (acc : List SourceJson) :
    momentRecordsBlock007Push acc = [momentJsonRecord031, momentJsonRecord030, momentJsonRecord029, momentJsonRecord028] ++ acc := by rfl

theorem moment_records_block_007_reverse (acc : List SourceJson) :
    (momentRecordsBlock007Push acc).reverse = acc.reverse ++ momentJsonRecordsBlock007 := by
  rw [moment_records_block_007_push_eq, List.reverse_append]
  rfl

theorem decode_moment_records_block_007 :
    momentJsonRecordsBlock007.mapM decodeMomentRecord = .ok momentTypedRecordsBlock007 := by
  simp only [momentJsonRecordsBlock007, momentTypedRecordsBlock007, List.mapM_cons, List.mapM_nil,
    decode_moment_record_028, decode_moment_record_029, decode_moment_record_030, decode_moment_record_031]
  rfl

noncomputable def momentTypedRowsThroughBlock007 : List MomentRecord := momentTypedRowsThroughBlock006 ++ momentTypedRecordsBlock007

theorem decode_moment_records_through_block_007 :
    momentRecordsAcc032.reverse.mapM decodeMomentRecord = .ok momentTypedRowsThroughBlock007 := by
  change (momentRecordsBlock007Push momentRecordsAcc028).reverse.mapM decodeMomentRecord = _
  rw [moment_records_block_007_reverse]
  rw [List.mapM_append, decode_moment_records_through_block_006, decode_moment_records_block_007]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_block_007_complete"
  err.flush

#print axioms moment_record_028_push_eq
#print axioms decode_moment_record_028
#print axioms moment_record_029_push_eq
#print axioms decode_moment_record_029
#print axioms moment_record_030_push_eq
#print axioms decode_moment_record_030
#print axioms moment_record_031_push_eq
#print axioms decode_moment_record_031
#print axioms moment_records_block_007_push_eq
#print axioms moment_records_block_007_reverse
#print axioms decode_moment_records_block_007
#print axioms decode_moment_records_through_block_007

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
