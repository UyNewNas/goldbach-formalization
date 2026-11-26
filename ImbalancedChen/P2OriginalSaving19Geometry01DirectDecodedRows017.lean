import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows016

/-! Original simplices typed block 17, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson034 : SourceJson :=
  (SimplicesBlock017.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped034 : GeometryRow :=
  { simplexId := 34,
    vertexIds := #[39, 35, 24, 11, 9, 7, 6, 2, 0],
    physicalVolume := ((80221788588320187283818988489943585199427 : ℚ) / (17163418116096000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((9233771 : ℚ) / (168000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((13512485953 : ℚ) / (159600000000 : ℚ)), ((95762816911 : ℚ) / (1117200000000 : ℚ)), ((31906581619 : ℚ) / (223440000000 : ℚ)), ((187483164329 : ℚ) / (1675800000000 : ℚ)), ((67395911159 : ℚ) / (1117200000000 : ℚ)), ((55494361357 : ℚ) / (1117200000000 : ℚ)), ((46460275063 : ℚ) / (1117200000000 : ℚ)), ((40378476683 : ℚ) / (1117200000000 : ℚ)), ((40378327723 : ℚ) / (1117200000000 : ℚ)), ((110691590267 : ℚ) / (3351600000000 : ℚ))],
    jensenBound := ((13341341203254079744535176543530936236039290481403284445444711584202240000000000000000000000 : ℚ) / (760958736094898222273800094690731930070787149328192639389579911860392978120021917903814631347574245891149 : ℚ)),
    jensenFloorQ96 := (1389050284689611 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_simplexId_before"
  err.flush

theorem geometryRow034_simplexId_read :
    geometryRowsJson034.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped034.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_vertexIds_before"
  err.flush

theorem geometryRow034_vertexIds_read :
    geometryRowsJson034.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped034.vertexIds := by decide +kernel

noncomputable def geometryRow034_physicalVolumeNumeratorChars : List Char := ['8', '0', '2', '2', '1', '7', '8', '8', '5', '8', '8', '3', '2', '0', '1', '8', '7', '2', '8', '3', '8', '1', '8', '9', '8', '8', '4', '8', '9', '9', '4', '3', '5', '8', '5', '1', '9', '9', '4', '2', '7']
noncomputable def geometryRow034_physicalVolumeDenominatorChars : List Char := ['1', '7', '1', '6', '3', '4', '1', '8', '1', '1', '6', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_physicalVolumeText : String := String.ofList (geometryRow034_physicalVolumeNumeratorChars ++ '/' :: geometryRow034_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_physicalVolume_before_field"
  err.flush

theorem geometryRow034_physicalVolume_field :
    geometryRowsJson034.getObjVal? "physical_volume" = .ok (.str geometryRow034_physicalVolumeText) := by rfl

theorem geometryRow034_physicalVolume_numerator_no_slash :
    geometryRow034_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow034_physicalVolumeNumeratorChars = some (80221788588320187283818988489943585199427 : Int) := by decide +kernel

theorem geometryRow034_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow034_physicalVolumeDenominatorChars = some (17163418116096000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow034_physicalVolume_denominator_nonzero : (17163418116096000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_physicalVolume_parse :
    parseRational geometryRow034_physicalVolumeText = .ok geometryRowsTyped034.physicalVolume :=
  original_rational_fraction_of_chars geometryRow034_physicalVolumeNumeratorChars geometryRow034_physicalVolumeDenominatorChars
    (80221788588320187283818988489943585199427 : Int) (17163418116096000000000000000000000000000000000000000000000000000 : Int)
    geometryRow034_physicalVolume_numerator_no_slash geometryRow034_physicalVolume_numerator_parse
    geometryRow034_physicalVolume_denominator_parse geometryRow034_physicalVolume_denominator_nonzero

theorem geometryRow034_physicalVolume_read :
    rationalField geometryRowsJson034 "physical_volume" = .ok geometryRowsTyped034.physicalVolume :=
  original_rationalField_of_string geometryRowsJson034 "physical_volume" geometryRow034_physicalVolumeText
    geometryRowsTyped034.physicalVolume geometryRow034_physicalVolume_field geometryRow034_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_physicalVolume_complete"
  err.flush

noncomputable def geometryRow034_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow034_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_meanGapText : String := String.ofList (geometryRow034_meanGapNumeratorChars ++ '/' :: geometryRow034_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_meanGap_before_field"
  err.flush

theorem geometryRow034_meanGap_field :
    geometryRowsJson034.getObjVal? "mean_gap" = .ok (.str geometryRow034_meanGapText) := by rfl

theorem geometryRow034_meanGap_numerator_no_slash :
    geometryRow034_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_meanGap_numerator_parse :
    SourceJson.intChars geometryRow034_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow034_meanGap_denominator_parse :
    SourceJson.intChars geometryRow034_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow034_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_meanGap_parse :
    parseRational geometryRow034_meanGapText = .ok geometryRowsTyped034.meanGap :=
  original_rational_fraction_of_chars geometryRow034_meanGapNumeratorChars geometryRow034_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow034_meanGap_numerator_no_slash geometryRow034_meanGap_numerator_parse
    geometryRow034_meanGap_denominator_parse geometryRow034_meanGap_denominator_nonzero

theorem geometryRow034_meanGap_read :
    rationalField geometryRowsJson034 "mean_gap" = .ok geometryRowsTyped034.meanGap :=
  original_rationalField_of_string geometryRowsJson034 "mean_gap" geometryRow034_meanGapText
    geometryRowsTyped034.meanGap geometryRow034_meanGap_field geometryRow034_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_meanGap_complete"
  err.flush

noncomputable def geometryRow034_jensenBoundNumeratorChars : List Char := ['1', '3', '3', '4', '1', '3', '4', '1', '2', '0', '3', '2', '5', '4', '0', '7', '9', '7', '4', '4', '5', '3', '5', '1', '7', '6', '5', '4', '3', '5', '3', '0', '9', '3', '6', '2', '3', '6', '0', '3', '9', '2', '9', '0', '4', '8', '1', '4', '0', '3', '2', '8', '4', '4', '4', '5', '4', '4', '4', '7', '1', '1', '5', '8', '4', '2', '0', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_jensenBoundDenominatorChars : List Char := ['7', '6', '0', '9', '5', '8', '7', '3', '6', '0', '9', '4', '8', '9', '8', '2', '2', '2', '2', '7', '3', '8', '0', '0', '0', '9', '4', '6', '9', '0', '7', '3', '1', '9', '3', '0', '0', '7', '0', '7', '8', '7', '1', '4', '9', '3', '2', '8', '1', '9', '2', '6', '3', '9', '3', '8', '9', '5', '7', '9', '9', '1', '1', '8', '6', '0', '3', '9', '2', '9', '7', '8', '1', '2', '0', '0', '2', '1', '9', '1', '7', '9', '0', '3', '8', '1', '4', '6', '3', '1', '3', '4', '7', '5', '7', '4', '2', '4', '5', '8', '9', '1', '1', '4', '9']
noncomputable def geometryRow034_jensenBoundText : String := String.ofList (geometryRow034_jensenBoundNumeratorChars ++ '/' :: geometryRow034_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_jensenBound_before_field"
  err.flush

theorem geometryRow034_jensenBound_field :
    geometryRowsJson034.getObjVal? "jensen_bound" = .ok (.str geometryRow034_jensenBoundText) := by rfl

theorem geometryRow034_jensenBound_numerator_no_slash :
    geometryRow034_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow034_jensenBoundNumeratorChars = some (13341341203254079744535176543530936236039290481403284445444711584202240000000000000000000000 : Int) := by decide +kernel

theorem geometryRow034_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow034_jensenBoundDenominatorChars = some (760958736094898222273800094690731930070787149328192639389579911860392978120021917903814631347574245891149 : Int) := by decide +kernel

theorem geometryRow034_jensenBound_denominator_nonzero : (760958736094898222273800094690731930070787149328192639389579911860392978120021917903814631347574245891149 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_jensenBound_parse :
    parseRational geometryRow034_jensenBoundText = .ok geometryRowsTyped034.jensenBound :=
  original_rational_fraction_of_chars geometryRow034_jensenBoundNumeratorChars geometryRow034_jensenBoundDenominatorChars
    (13341341203254079744535176543530936236039290481403284445444711584202240000000000000000000000 : Int) (760958736094898222273800094690731930070787149328192639389579911860392978120021917903814631347574245891149 : Int)
    geometryRow034_jensenBound_numerator_no_slash geometryRow034_jensenBound_numerator_parse
    geometryRow034_jensenBound_denominator_parse geometryRow034_jensenBound_denominator_nonzero

theorem geometryRow034_jensenBound_read :
    rationalField geometryRowsJson034 "jensen_bound" = .ok geometryRowsTyped034.jensenBound :=
  original_rationalField_of_string geometryRowsJson034 "jensen_bound" geometryRow034_jensenBoundText
    geometryRowsTyped034.jensenBound geometryRow034_jensenBound_field geometryRow034_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_factorMaxima_before"
  err.flush

theorem geometryRow034_factorMaxima_read :
    rationalArrayField geometryRowsJson034 "factor_maxima" = .ok geometryRowsTyped034.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_gapWeightedMeans_before"
  err.flush

theorem geometryRow034_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson034 "gap_weighted_means" = .ok geometryRowsTyped034.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow034_floorChars : List Char := ['1', '3', '8', '9', '0', '5', '0', '2', '8', '4', '6', '8', '9', '6', '1', '1']
noncomputable def geometryRow034_floorText : String := String.ofList geometryRow034_floorChars

theorem geometryRow034_floor_text_read :
    geometryRowsJson034.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow034_floorText := by rfl

theorem geometryRow034_floor_chars_parse :
    SourceJson.intChars geometryRow034_floorChars = some (1389050284689611 : Int) := by decide +kernel

theorem geometryRow034_floor_parse :
    parseInteger geometryRow034_floorText = .ok geometryRowsTyped034.jensenFloorQ96 := by
  simp only [geometryRow034_floorText, parseInteger, String.toList_ofList, geometryRow034_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_034 :
    decodeGeometryRow geometryRowsJson034 = .ok geometryRowsTyped034 :=
  original_geometryRow_of_fields geometryRowsJson034 geometryRowsTyped034 geometryRow034_floorText
    geometryRow034_simplexId_read geometryRow034_vertexIds_read
    geometryRow034_physicalVolume_read geometryRow034_meanGap_read
    geometryRow034_factorMaxima_read geometryRow034_gapWeightedMeans_read
    geometryRow034_jensenBound_read geometryRow034_floor_text_read geometryRow034_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_034_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson035 : SourceJson :=
  (SimplicesBlock017.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped035 : GeometryRow :=
  { simplexId := 35,
    vertexIds := #[39, 35, 24, 23, 10, 8, 3, 1, 0],
    physicalVolume := ((203975737479981629787818395089164893 : ℚ) / (271481241600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((1004422423723 : ℚ) / (11757200000000 : ℚ)), ((1016307085603 : ℚ) / (11757200000000 : ℚ)), ((1161786011821 : ℚ) / (8139600000000 : ℚ)), ((1926661579061 : ℚ) / (17635800000000 : ℚ)), ((375565135837 : ℚ) / (6224400000000 : ℚ)), ((5279662763747 : ℚ) / (105814800000000 : ℚ)), ((217718236963 : ℚ) / (5569200000000 : ℚ)), ((4080144833437 : ℚ) / (105814800000000 : ℚ)), ((3757405385707 : ℚ) / (105814800000000 : ℚ)), ((3757384222747 : ℚ) / (105814800000000 : ℚ))],
    jensenBound := ((45869186112057271703898218832040994243946406301568514325878716989896494791491392000000000000000000000000 : ℚ) / (17907640324412093955292627864996877428807278595033696882264687081361418704123582263748694314498981751401772209575597973 : ℚ)),
    jensenFloorQ96 := (202937476174847 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_simplexId_before"
  err.flush

theorem geometryRow035_simplexId_read :
    geometryRowsJson035.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped035.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_vertexIds_before"
  err.flush

theorem geometryRow035_vertexIds_read :
    geometryRowsJson035.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped035.vertexIds := by decide +kernel

noncomputable def geometryRow035_physicalVolumeNumeratorChars : List Char := ['2', '0', '3', '9', '7', '5', '7', '3', '7', '4', '7', '9', '9', '8', '1', '6', '2', '9', '7', '8', '7', '8', '1', '8', '3', '9', '5', '0', '8', '9', '1', '6', '4', '8', '9', '3']
noncomputable def geometryRow035_physicalVolumeDenominatorChars : List Char := ['2', '7', '1', '4', '8', '1', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_physicalVolumeText : String := String.ofList (geometryRow035_physicalVolumeNumeratorChars ++ '/' :: geometryRow035_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_physicalVolume_before_field"
  err.flush

theorem geometryRow035_physicalVolume_field :
    geometryRowsJson035.getObjVal? "physical_volume" = .ok (.str geometryRow035_physicalVolumeText) := by rfl

theorem geometryRow035_physicalVolume_numerator_no_slash :
    geometryRow035_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow035_physicalVolumeNumeratorChars = some (203975737479981629787818395089164893 : Int) := by decide +kernel

theorem geometryRow035_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow035_physicalVolumeDenominatorChars = some (271481241600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow035_physicalVolume_denominator_nonzero : (271481241600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_physicalVolume_parse :
    parseRational geometryRow035_physicalVolumeText = .ok geometryRowsTyped035.physicalVolume :=
  original_rational_fraction_of_chars geometryRow035_physicalVolumeNumeratorChars geometryRow035_physicalVolumeDenominatorChars
    (203975737479981629787818395089164893 : Int) (271481241600000000000000000000000000000000000000000000000000 : Int)
    geometryRow035_physicalVolume_numerator_no_slash geometryRow035_physicalVolume_numerator_parse
    geometryRow035_physicalVolume_denominator_parse geometryRow035_physicalVolume_denominator_nonzero

theorem geometryRow035_physicalVolume_read :
    rationalField geometryRowsJson035 "physical_volume" = .ok geometryRowsTyped035.physicalVolume :=
  original_rationalField_of_string geometryRowsJson035 "physical_volume" geometryRow035_physicalVolumeText
    geometryRowsTyped035.physicalVolume geometryRow035_physicalVolume_field geometryRow035_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_physicalVolume_complete"
  err.flush

noncomputable def geometryRow035_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow035_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_meanGapText : String := String.ofList (geometryRow035_meanGapNumeratorChars ++ '/' :: geometryRow035_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_meanGap_before_field"
  err.flush

theorem geometryRow035_meanGap_field :
    geometryRowsJson035.getObjVal? "mean_gap" = .ok (.str geometryRow035_meanGapText) := by rfl

theorem geometryRow035_meanGap_numerator_no_slash :
    geometryRow035_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_meanGap_numerator_parse :
    SourceJson.intChars geometryRow035_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow035_meanGap_denominator_parse :
    SourceJson.intChars geometryRow035_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow035_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_meanGap_parse :
    parseRational geometryRow035_meanGapText = .ok geometryRowsTyped035.meanGap :=
  original_rational_fraction_of_chars geometryRow035_meanGapNumeratorChars geometryRow035_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow035_meanGap_numerator_no_slash geometryRow035_meanGap_numerator_parse
    geometryRow035_meanGap_denominator_parse geometryRow035_meanGap_denominator_nonzero

theorem geometryRow035_meanGap_read :
    rationalField geometryRowsJson035 "mean_gap" = .ok geometryRowsTyped035.meanGap :=
  original_rationalField_of_string geometryRowsJson035 "mean_gap" geometryRow035_meanGapText
    geometryRowsTyped035.meanGap geometryRow035_meanGap_field geometryRow035_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_meanGap_complete"
  err.flush

noncomputable def geometryRow035_jensenBoundNumeratorChars : List Char := ['4', '5', '8', '6', '9', '1', '8', '6', '1', '1', '2', '0', '5', '7', '2', '7', '1', '7', '0', '3', '8', '9', '8', '2', '1', '8', '8', '3', '2', '0', '4', '0', '9', '9', '4', '2', '4', '3', '9', '4', '6', '4', '0', '6', '3', '0', '1', '5', '6', '8', '5', '1', '4', '3', '2', '5', '8', '7', '8', '7', '1', '6', '9', '8', '9', '8', '9', '6', '4', '9', '4', '7', '9', '1', '4', '9', '1', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_jensenBoundDenominatorChars : List Char := ['1', '7', '9', '0', '7', '6', '4', '0', '3', '2', '4', '4', '1', '2', '0', '9', '3', '9', '5', '5', '2', '9', '2', '6', '2', '7', '8', '6', '4', '9', '9', '6', '8', '7', '7', '4', '2', '8', '8', '0', '7', '2', '7', '8', '5', '9', '5', '0', '3', '3', '6', '9', '6', '8', '8', '2', '2', '6', '4', '6', '8', '7', '0', '8', '1', '3', '6', '1', '4', '1', '8', '7', '0', '4', '1', '2', '3', '5', '8', '2', '2', '6', '3', '7', '4', '8', '6', '9', '4', '3', '1', '4', '4', '9', '8', '9', '8', '1', '7', '5', '1', '4', '0', '1', '7', '7', '2', '2', '0', '9', '5', '7', '5', '5', '9', '7', '9', '7', '3']
noncomputable def geometryRow035_jensenBoundText : String := String.ofList (geometryRow035_jensenBoundNumeratorChars ++ '/' :: geometryRow035_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_jensenBound_before_field"
  err.flush

theorem geometryRow035_jensenBound_field :
    geometryRowsJson035.getObjVal? "jensen_bound" = .ok (.str geometryRow035_jensenBoundText) := by rfl

theorem geometryRow035_jensenBound_numerator_no_slash :
    geometryRow035_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow035_jensenBoundNumeratorChars = some (45869186112057271703898218832040994243946406301568514325878716989896494791491392000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow035_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow035_jensenBoundDenominatorChars = some (17907640324412093955292627864996877428807278595033696882264687081361418704123582263748694314498981751401772209575597973 : Int) := by decide +kernel

theorem geometryRow035_jensenBound_denominator_nonzero : (17907640324412093955292627864996877428807278595033696882264687081361418704123582263748694314498981751401772209575597973 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_jensenBound_parse :
    parseRational geometryRow035_jensenBoundText = .ok geometryRowsTyped035.jensenBound :=
  original_rational_fraction_of_chars geometryRow035_jensenBoundNumeratorChars geometryRow035_jensenBoundDenominatorChars
    (45869186112057271703898218832040994243946406301568514325878716989896494791491392000000000000000000000000 : Int) (17907640324412093955292627864996877428807278595033696882264687081361418704123582263748694314498981751401772209575597973 : Int)
    geometryRow035_jensenBound_numerator_no_slash geometryRow035_jensenBound_numerator_parse
    geometryRow035_jensenBound_denominator_parse geometryRow035_jensenBound_denominator_nonzero

theorem geometryRow035_jensenBound_read :
    rationalField geometryRowsJson035 "jensen_bound" = .ok geometryRowsTyped035.jensenBound :=
  original_rationalField_of_string geometryRowsJson035 "jensen_bound" geometryRow035_jensenBoundText
    geometryRowsTyped035.jensenBound geometryRow035_jensenBound_field geometryRow035_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_factorMaxima_before"
  err.flush

theorem geometryRow035_factorMaxima_read :
    rationalArrayField geometryRowsJson035 "factor_maxima" = .ok geometryRowsTyped035.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_gapWeightedMeans_before"
  err.flush

theorem geometryRow035_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson035 "gap_weighted_means" = .ok geometryRowsTyped035.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow035_floorChars : List Char := ['2', '0', '2', '9', '3', '7', '4', '7', '6', '1', '7', '4', '8', '4', '7']
noncomputable def geometryRow035_floorText : String := String.ofList geometryRow035_floorChars

theorem geometryRow035_floor_text_read :
    geometryRowsJson035.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow035_floorText := by rfl

theorem geometryRow035_floor_chars_parse :
    SourceJson.intChars geometryRow035_floorChars = some (202937476174847 : Int) := by decide +kernel

theorem geometryRow035_floor_parse :
    parseInteger geometryRow035_floorText = .ok geometryRowsTyped035.jensenFloorQ96 := by
  simp only [geometryRow035_floorText, parseInteger, String.toList_ofList, geometryRow035_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_035 :
    decodeGeometryRow geometryRowsJson035 = .ok geometryRowsTyped035 :=
  original_geometryRow_of_fields geometryRowsJson035 geometryRowsTyped035 geometryRow035_floorText
    geometryRow035_simplexId_read geometryRow035_vertexIds_read
    geometryRow035_physicalVolume_read geometryRow035_meanGap_read
    geometryRow035_factorMaxima_read geometryRow035_gapWeightedMeans_read
    geometryRow035_jensenBound_read geometryRow035_floor_text_read geometryRow035_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_035_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock017 : List SourceJson := [geometryRowsJson034, geometryRowsJson035]
noncomputable def geometryRowsTypedBlock017 : List (GeometryRow) := [geometryRowsTyped034, geometryRowsTyped035]
noncomputable def geometryRowsTypedThroughBlock017 : List (GeometryRow) := geometryRowsTypedThroughBlock016 ++ geometryRowsTypedBlock017

theorem geometry_Rows_block_017_push_eq (acc : List SourceJson) :
    SimplicesBlock017.blockPush acc = [geometryRowsJson035, geometryRowsJson034] ++ acc := by rfl

theorem geometry_Rows_block_017_reverse (acc : List SourceJson) :
    (SimplicesBlock017.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock017 := by
  rw [geometry_Rows_block_017_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_017 :
    geometryRowsJsonBlock017.mapM decodeGeometryRow = .ok geometryRowsTypedBlock017 := by
  simp only [geometryRowsJsonBlock017, geometryRowsTypedBlock017, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_034, decode_geometry_Rows_035]
  rfl

theorem decode_geometry_Rows_through_block_017 :
    SimplicesValue.arrayAcc018.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock017 := by
  change (SimplicesBlock017.blockPush SimplicesValue.arrayAcc017).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_017_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_016, decode_geometry_Rows_block_017]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_017_complete"
  err.flush

#print axioms geometryRow034_simplexId_read
#print axioms geometryRow034_vertexIds_read
#print axioms geometryRow034_physicalVolume_field
#print axioms geometryRow034_physicalVolume_numerator_no_slash
#print axioms geometryRow034_physicalVolume_numerator_parse
#print axioms geometryRow034_physicalVolume_denominator_parse
#print axioms geometryRow034_physicalVolume_denominator_nonzero
#print axioms geometryRow034_physicalVolume_parse
#print axioms geometryRow034_physicalVolume_read
#print axioms geometryRow034_meanGap_field
#print axioms geometryRow034_meanGap_numerator_no_slash
#print axioms geometryRow034_meanGap_numerator_parse
#print axioms geometryRow034_meanGap_denominator_parse
#print axioms geometryRow034_meanGap_denominator_nonzero
#print axioms geometryRow034_meanGap_parse
#print axioms geometryRow034_meanGap_read
#print axioms geometryRow034_jensenBound_field
#print axioms geometryRow034_jensenBound_numerator_no_slash
#print axioms geometryRow034_jensenBound_numerator_parse
#print axioms geometryRow034_jensenBound_denominator_parse
#print axioms geometryRow034_jensenBound_denominator_nonzero
#print axioms geometryRow034_jensenBound_parse
#print axioms geometryRow034_jensenBound_read
#print axioms geometryRow034_factorMaxima_read
#print axioms geometryRow034_gapWeightedMeans_read
#print axioms geometryRow034_floor_text_read
#print axioms geometryRow034_floor_chars_parse
#print axioms geometryRow034_floor_parse
#print axioms decode_geometry_Rows_034
#print axioms geometryRow035_simplexId_read
#print axioms geometryRow035_vertexIds_read
#print axioms geometryRow035_physicalVolume_field
#print axioms geometryRow035_physicalVolume_numerator_no_slash
#print axioms geometryRow035_physicalVolume_numerator_parse
#print axioms geometryRow035_physicalVolume_denominator_parse
#print axioms geometryRow035_physicalVolume_denominator_nonzero
#print axioms geometryRow035_physicalVolume_parse
#print axioms geometryRow035_physicalVolume_read
#print axioms geometryRow035_meanGap_field
#print axioms geometryRow035_meanGap_numerator_no_slash
#print axioms geometryRow035_meanGap_numerator_parse
#print axioms geometryRow035_meanGap_denominator_parse
#print axioms geometryRow035_meanGap_denominator_nonzero
#print axioms geometryRow035_meanGap_parse
#print axioms geometryRow035_meanGap_read
#print axioms geometryRow035_jensenBound_field
#print axioms geometryRow035_jensenBound_numerator_no_slash
#print axioms geometryRow035_jensenBound_numerator_parse
#print axioms geometryRow035_jensenBound_denominator_parse
#print axioms geometryRow035_jensenBound_denominator_nonzero
#print axioms geometryRow035_jensenBound_parse
#print axioms geometryRow035_jensenBound_read
#print axioms geometryRow035_factorMaxima_read
#print axioms geometryRow035_gapWeightedMeans_read
#print axioms geometryRow035_floor_text_read
#print axioms geometryRow035_floor_chars_parse
#print axioms geometryRow035_floor_parse
#print axioms decode_geometry_Rows_035
#print axioms geometry_Rows_block_017_push_eq
#print axioms geometry_Rows_block_017_reverse
#print axioms decode_geometry_Rows_block_017
#print axioms decode_geometry_Rows_through_block_017

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
