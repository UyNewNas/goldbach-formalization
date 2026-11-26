import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows046

/-! Original simplices typed block 47, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson093 : SourceJson :=
  (SimplicesBlock047.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped093 : GeometryRow :=
  { simplexId := 93,
    vertexIds := #[39, 37, 24, 23, 21, 20, 19, 2, 0],
    physicalVolume := ((14645942979409673167518599587551095373605761 : ℚ) / (507995146065852204318720000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((899153113 : ℚ) / (1110193000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((957 : ℚ) / (20864 : ℚ))],
    gapWeightedMeans := #[((3522618342014321989268347 : ℚ) / (43661510612515711200000000 : ℚ)), ((58346918712351331209108111 : ℚ) / (713138006671089949600000000 : ℚ)), ((934087621744717068678330611 : ℚ) / (6418242060039809546400000000 : ℚ)), ((348229003029909365697447697 : ℚ) / (3209121030019904773200000000 : ℚ)), ((343601181995779685408949941 : ℚ) / (6418242060039809546400000000 : ℚ)), ((304036437818210258307005833 : ℚ) / (6418242060039809546400000000 : ℚ)), ((2772162513958665245177051 : ℚ) / (67560442737261153120000000 : ℚ)), ((51985661175475409309852873 : ℚ) / (1283648412007961909280000000 : ℚ)), ((85551324921385133939458409 : ℚ) / (2139414020013269848800000000 : ℚ)), ((28026355159903523757953333 : ℚ) / (713138006671089949600000000 : ℚ))],
    jensenBound := ((108720467594322753013873447338461324083627906080512612086100768845166849431357849835052009081568985995363950292341282139746444892737483986167008331418224203115112981256594013778170207456328092380094405031246199091200000000000000000000000000000 : ℚ) / (803630935712753299026813490112164195198094419250477332718207811592926258665896865525673785274533007252294258365402056275232537720849670248114499082797380758247409116461720742234242777627534476263589755059815795831610487595998100208170804831698560829158959 : ℚ)),
    jensenFloorQ96 := (10718505836948850 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_simplexId_before"
  err.flush

theorem geometryRow093_simplexId_read :
    geometryRowsJson093.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped093.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_vertexIds_before"
  err.flush

theorem geometryRow093_vertexIds_read :
    geometryRowsJson093.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped093.vertexIds := by decide +kernel

noncomputable def geometryRow093_physicalVolumeNumeratorChars : List Char := ['1', '4', '6', '4', '5', '9', '4', '2', '9', '7', '9', '4', '0', '9', '6', '7', '3', '1', '6', '7', '5', '1', '8', '5', '9', '9', '5', '8', '7', '5', '5', '1', '0', '9', '5', '3', '7', '3', '6', '0', '5', '7', '6', '1']
noncomputable def geometryRow093_physicalVolumeDenominatorChars : List Char := ['5', '0', '7', '9', '9', '5', '1', '4', '6', '0', '6', '5', '8', '5', '2', '2', '0', '4', '3', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow093_physicalVolumeText : String := String.ofList (geometryRow093_physicalVolumeNumeratorChars ++ '/' :: geometryRow093_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_physicalVolume_before_field"
  err.flush

theorem geometryRow093_physicalVolume_field :
    geometryRowsJson093.getObjVal? "physical_volume" = .ok (.str geometryRow093_physicalVolumeText) := by rfl

theorem geometryRow093_physicalVolume_numerator_no_slash :
    geometryRow093_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow093_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow093_physicalVolumeNumeratorChars = some (14645942979409673167518599587551095373605761 : Int) := by decide +kernel

theorem geometryRow093_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow093_physicalVolumeDenominatorChars = some (507995146065852204318720000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow093_physicalVolume_denominator_nonzero : (507995146065852204318720000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow093_physicalVolume_parse :
    parseRational geometryRow093_physicalVolumeText = .ok geometryRowsTyped093.physicalVolume :=
  original_rational_fraction_of_chars geometryRow093_physicalVolumeNumeratorChars geometryRow093_physicalVolumeDenominatorChars
    (14645942979409673167518599587551095373605761 : Int) (507995146065852204318720000000000000000000000000000000000000000000 : Int)
    geometryRow093_physicalVolume_numerator_no_slash geometryRow093_physicalVolume_numerator_parse
    geometryRow093_physicalVolume_denominator_parse geometryRow093_physicalVolume_denominator_nonzero

theorem geometryRow093_physicalVolume_read :
    rationalField geometryRowsJson093 "physical_volume" = .ok geometryRowsTyped093.physicalVolume :=
  original_rationalField_of_string geometryRowsJson093 "physical_volume" geometryRow093_physicalVolumeText
    geometryRowsTyped093.physicalVolume geometryRow093_physicalVolume_field geometryRow093_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_physicalVolume_complete"
  err.flush

noncomputable def geometryRow093_meanGapNumeratorChars : List Char := ['8', '9', '9', '1', '5', '3', '1', '1', '3']
noncomputable def geometryRow093_meanGapDenominatorChars : List Char := ['1', '1', '1', '0', '1', '9', '3', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow093_meanGapText : String := String.ofList (geometryRow093_meanGapNumeratorChars ++ '/' :: geometryRow093_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_meanGap_before_field"
  err.flush

theorem geometryRow093_meanGap_field :
    geometryRowsJson093.getObjVal? "mean_gap" = .ok (.str geometryRow093_meanGapText) := by rfl

theorem geometryRow093_meanGap_numerator_no_slash :
    geometryRow093_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow093_meanGap_numerator_parse :
    SourceJson.intChars geometryRow093_meanGapNumeratorChars = some (899153113 : Int) := by decide +kernel

theorem geometryRow093_meanGap_denominator_parse :
    SourceJson.intChars geometryRow093_meanGapDenominatorChars = some (1110193000000 : Int) := by decide +kernel

theorem geometryRow093_meanGap_denominator_nonzero : (1110193000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow093_meanGap_parse :
    parseRational geometryRow093_meanGapText = .ok geometryRowsTyped093.meanGap :=
  original_rational_fraction_of_chars geometryRow093_meanGapNumeratorChars geometryRow093_meanGapDenominatorChars
    (899153113 : Int) (1110193000000 : Int)
    geometryRow093_meanGap_numerator_no_slash geometryRow093_meanGap_numerator_parse
    geometryRow093_meanGap_denominator_parse geometryRow093_meanGap_denominator_nonzero

theorem geometryRow093_meanGap_read :
    rationalField geometryRowsJson093 "mean_gap" = .ok geometryRowsTyped093.meanGap :=
  original_rationalField_of_string geometryRowsJson093 "mean_gap" geometryRow093_meanGapText
    geometryRowsTyped093.meanGap geometryRow093_meanGap_field geometryRow093_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_meanGap_complete"
  err.flush

noncomputable def geometryRow093_jensenBoundNumeratorChars : List Char := ['1', '0', '8', '7', '2', '0', '4', '6', '7', '5', '9', '4', '3', '2', '2', '7', '5', '3', '0', '1', '3', '8', '7', '3', '4', '4', '7', '3', '3', '8', '4', '6', '1', '3', '2', '4', '0', '8', '3', '6', '2', '7', '9', '0', '6', '0', '8', '0', '5', '1', '2', '6', '1', '2', '0', '8', '6', '1', '0', '0', '7', '6', '8', '8', '4', '5', '1', '6', '6', '8', '4', '9', '4', '3', '1', '3', '5', '7', '8', '4', '9', '8', '3', '5', '0', '5', '2', '0', '0', '9', '0', '8', '1', '5', '6', '8', '9', '8', '5', '9', '9', '5', '3', '6', '3', '9', '5', '0', '2', '9', '2', '3', '4', '1', '2', '8', '2', '1', '3', '9', '7', '4', '6', '4', '4', '4', '8', '9', '2', '7', '3', '7', '4', '8', '3', '9', '8', '6', '1', '6', '7', '0', '0', '8', '3', '3', '1', '4', '1', '8', '2', '2', '4', '2', '0', '3', '1', '1', '5', '1', '1', '2', '9', '8', '1', '2', '5', '6', '5', '9', '4', '0', '1', '3', '7', '7', '8', '1', '7', '0', '2', '0', '7', '4', '5', '6', '3', '2', '8', '0', '9', '2', '3', '8', '0', '0', '9', '4', '4', '0', '5', '0', '3', '1', '2', '4', '6', '1', '9', '9', '0', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow093_jensenBoundDenominatorChars : List Char := ['8', '0', '3', '6', '3', '0', '9', '3', '5', '7', '1', '2', '7', '5', '3', '2', '9', '9', '0', '2', '6', '8', '1', '3', '4', '9', '0', '1', '1', '2', '1', '6', '4', '1', '9', '5', '1', '9', '8', '0', '9', '4', '4', '1', '9', '2', '5', '0', '4', '7', '7', '3', '3', '2', '7', '1', '8', '2', '0', '7', '8', '1', '1', '5', '9', '2', '9', '2', '6', '2', '5', '8', '6', '6', '5', '8', '9', '6', '8', '6', '5', '5', '2', '5', '6', '7', '3', '7', '8', '5', '2', '7', '4', '5', '3', '3', '0', '0', '7', '2', '5', '2', '2', '9', '4', '2', '5', '8', '3', '6', '5', '4', '0', '2', '0', '5', '6', '2', '7', '5', '2', '3', '2', '5', '3', '7', '7', '2', '0', '8', '4', '9', '6', '7', '0', '2', '4', '8', '1', '1', '4', '4', '9', '9', '0', '8', '2', '7', '9', '7', '3', '8', '0', '7', '5', '8', '2', '4', '7', '4', '0', '9', '1', '1', '6', '4', '6', '1', '7', '2', '0', '7', '4', '2', '2', '3', '4', '2', '4', '2', '7', '7', '7', '6', '2', '7', '5', '3', '4', '4', '7', '6', '2', '6', '3', '5', '8', '9', '7', '5', '5', '0', '5', '9', '8', '1', '5', '7', '9', '5', '8', '3', '1', '6', '1', '0', '4', '8', '7', '5', '9', '5', '9', '9', '8', '1', '0', '0', '2', '0', '8', '1', '7', '0', '8', '0', '4', '8', '3', '1', '6', '9', '8', '5', '6', '0', '8', '2', '9', '1', '5', '8', '9', '5', '9']
noncomputable def geometryRow093_jensenBoundText : String := String.ofList (geometryRow093_jensenBoundNumeratorChars ++ '/' :: geometryRow093_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_jensenBound_before_field"
  err.flush

theorem geometryRow093_jensenBound_field :
    geometryRowsJson093.getObjVal? "jensen_bound" = .ok (.str geometryRow093_jensenBoundText) := by rfl

theorem geometryRow093_jensenBound_numerator_no_slash :
    geometryRow093_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow093_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow093_jensenBoundNumeratorChars = some (108720467594322753013873447338461324083627906080512612086100768845166849431357849835052009081568985995363950292341282139746444892737483986167008331418224203115112981256594013778170207456328092380094405031246199091200000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow093_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow093_jensenBoundDenominatorChars = some (803630935712753299026813490112164195198094419250477332718207811592926258665896865525673785274533007252294258365402056275232537720849670248114499082797380758247409116461720742234242777627534476263589755059815795831610487595998100208170804831698560829158959 : Int) := by decide +kernel

theorem geometryRow093_jensenBound_denominator_nonzero : (803630935712753299026813490112164195198094419250477332718207811592926258665896865525673785274533007252294258365402056275232537720849670248114499082797380758247409116461720742234242777627534476263589755059815795831610487595998100208170804831698560829158959 : Int) ≠ 0 := by decide +kernel

theorem geometryRow093_jensenBound_parse :
    parseRational geometryRow093_jensenBoundText = .ok geometryRowsTyped093.jensenBound :=
  original_rational_fraction_of_chars geometryRow093_jensenBoundNumeratorChars geometryRow093_jensenBoundDenominatorChars
    (108720467594322753013873447338461324083627906080512612086100768845166849431357849835052009081568985995363950292341282139746444892737483986167008331418224203115112981256594013778170207456328092380094405031246199091200000000000000000000000000000 : Int) (803630935712753299026813490112164195198094419250477332718207811592926258665896865525673785274533007252294258365402056275232537720849670248114499082797380758247409116461720742234242777627534476263589755059815795831610487595998100208170804831698560829158959 : Int)
    geometryRow093_jensenBound_numerator_no_slash geometryRow093_jensenBound_numerator_parse
    geometryRow093_jensenBound_denominator_parse geometryRow093_jensenBound_denominator_nonzero

theorem geometryRow093_jensenBound_read :
    rationalField geometryRowsJson093 "jensen_bound" = .ok geometryRowsTyped093.jensenBound :=
  original_rationalField_of_string geometryRowsJson093 "jensen_bound" geometryRow093_jensenBoundText
    geometryRowsTyped093.jensenBound geometryRow093_jensenBound_field geometryRow093_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_factorMaxima_before"
  err.flush

theorem geometryRow093_factorMaxima_read :
    rationalArrayField geometryRowsJson093 "factor_maxima" = .ok geometryRowsTyped093.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_gapWeightedMeans_before"
  err.flush

theorem geometryRow093_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson093 "gap_weighted_means" = .ok geometryRowsTyped093.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow093_floorChars : List Char := ['1', '0', '7', '1', '8', '5', '0', '5', '8', '3', '6', '9', '4', '8', '8', '5', '0']
noncomputable def geometryRow093_floorText : String := String.ofList geometryRow093_floorChars

theorem geometryRow093_floor_text_read :
    geometryRowsJson093.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow093_floorText := by rfl

theorem geometryRow093_floor_chars_parse :
    SourceJson.intChars geometryRow093_floorChars = some (10718505836948850 : Int) := by decide +kernel

theorem geometryRow093_floor_parse :
    parseInteger geometryRow093_floorText = .ok geometryRowsTyped093.jensenFloorQ96 := by
  simp only [geometryRow093_floorText, parseInteger, String.toList_ofList, geometryRow093_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_093 :
    decodeGeometryRow geometryRowsJson093 = .ok geometryRowsTyped093 :=
  original_geometryRow_of_fields geometryRowsJson093 geometryRowsTyped093 geometryRow093_floorText
    geometryRow093_simplexId_read geometryRow093_vertexIds_read
    geometryRow093_physicalVolume_read geometryRow093_meanGap_read
    geometryRow093_factorMaxima_read geometryRow093_gapWeightedMeans_read
    geometryRow093_jensenBound_read geometryRow093_floor_text_read geometryRow093_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_093_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock047 : List SourceJson := [geometryRowsJson093]
noncomputable def geometryRowsTypedBlock047 : List (GeometryRow) := [geometryRowsTyped093]
noncomputable def geometryRowsTypedThroughBlock047 : List (GeometryRow) := geometryRowsTypedThroughBlock046 ++ geometryRowsTypedBlock047

theorem geometry_Rows_block_047_push_eq (acc : List SourceJson) :
    SimplicesBlock047.blockPush acc = [geometryRowsJson093] ++ acc := by rfl

theorem geometry_Rows_block_047_reverse (acc : List SourceJson) :
    (SimplicesBlock047.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock047 := by
  rw [geometry_Rows_block_047_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_047 :
    geometryRowsJsonBlock047.mapM decodeGeometryRow = .ok geometryRowsTypedBlock047 := by
  simp only [geometryRowsJsonBlock047, geometryRowsTypedBlock047, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_093]
  rfl

theorem decode_geometry_Rows_through_block_047 :
    SimplicesValue.arrayAcc048.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock047 := by
  change (SimplicesBlock047.blockPush SimplicesValue.arrayAcc047).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_047_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_046, decode_geometry_Rows_block_047]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_047_complete"
  err.flush

#print axioms geometryRow093_simplexId_read
#print axioms geometryRow093_vertexIds_read
#print axioms geometryRow093_physicalVolume_field
#print axioms geometryRow093_physicalVolume_numerator_no_slash
#print axioms geometryRow093_physicalVolume_numerator_parse
#print axioms geometryRow093_physicalVolume_denominator_parse
#print axioms geometryRow093_physicalVolume_denominator_nonzero
#print axioms geometryRow093_physicalVolume_parse
#print axioms geometryRow093_physicalVolume_read
#print axioms geometryRow093_meanGap_field
#print axioms geometryRow093_meanGap_numerator_no_slash
#print axioms geometryRow093_meanGap_numerator_parse
#print axioms geometryRow093_meanGap_denominator_parse
#print axioms geometryRow093_meanGap_denominator_nonzero
#print axioms geometryRow093_meanGap_parse
#print axioms geometryRow093_meanGap_read
#print axioms geometryRow093_jensenBound_field
#print axioms geometryRow093_jensenBound_numerator_no_slash
#print axioms geometryRow093_jensenBound_numerator_parse
#print axioms geometryRow093_jensenBound_denominator_parse
#print axioms geometryRow093_jensenBound_denominator_nonzero
#print axioms geometryRow093_jensenBound_parse
#print axioms geometryRow093_jensenBound_read
#print axioms geometryRow093_factorMaxima_read
#print axioms geometryRow093_gapWeightedMeans_read
#print axioms geometryRow093_floor_text_read
#print axioms geometryRow093_floor_chars_parse
#print axioms geometryRow093_floor_parse
#print axioms decode_geometry_Rows_093
#print axioms geometry_Rows_block_047_push_eq
#print axioms geometry_Rows_block_047_reverse
#print axioms decode_geometry_Rows_block_047
#print axioms decode_geometry_Rows_through_block_047

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
