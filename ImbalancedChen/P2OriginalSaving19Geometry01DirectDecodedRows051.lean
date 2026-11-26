import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows050

/-! Original simplices typed block 51, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson100 : SourceJson :=
  (SimplicesBlock051.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped100 : GeometryRow :=
  { simplexId := 100,
    vertexIds := #[39, 37, 24, 23, 19, 18, 15, 7, 0],
    physicalVolume := ((360516992179449709901465825119672936748653097 : ℚ) / (1523624120460490309632000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((4077756143 : ℚ) / (51994687500 : ℚ)), ((52341029899 : ℚ) / (665532000000 : ℚ)), ((1461812645959 : ℚ) / (9982980000000 : ℚ)), ((238093205107 : ℚ) / (2218440000000 : ℚ)), ((207880839287 : ℚ) / (3993192000000 : ℚ)), ((120352340561 : ℚ) / (2495745000000 : ℚ)), ((44363872547 : ℚ) / (1050840000000 : ℚ)), ((832252403771 : ℚ) / (19965960000000 : ℚ)), ((206729788583 : ℚ) / (4991490000000 : ℚ)), ((789571453991 : ℚ) / (19965960000000 : ℚ))],
    jensenBound := ((2186684824222051146765179126936996014143505887582531815101268009349163029499051037850952148437500 : ℚ) / (13318467124927392763354237883787045513092690767308459557019483825841405320646265875804582803489408866884799927 : ℚ)),
    jensenFloorQ96 := (13008030052999413 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_simplexId_before"
  err.flush

theorem geometryRow100_simplexId_read :
    geometryRowsJson100.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped100.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_vertexIds_before"
  err.flush

theorem geometryRow100_vertexIds_read :
    geometryRowsJson100.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped100.vertexIds := by decide +kernel

noncomputable def geometryRow100_physicalVolumeNumeratorChars : List Char := ['3', '6', '0', '5', '1', '6', '9', '9', '2', '1', '7', '9', '4', '4', '9', '7', '0', '9', '9', '0', '1', '4', '6', '5', '8', '2', '5', '1', '1', '9', '6', '7', '2', '9', '3', '6', '7', '4', '8', '6', '5', '3', '0', '9', '7']
noncomputable def geometryRow100_physicalVolumeDenominatorChars : List Char := ['1', '5', '2', '3', '6', '2', '4', '1', '2', '0', '4', '6', '0', '4', '9', '0', '3', '0', '9', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow100_physicalVolumeText : String := String.ofList (geometryRow100_physicalVolumeNumeratorChars ++ '/' :: geometryRow100_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_physicalVolume_before_field"
  err.flush

theorem geometryRow100_physicalVolume_field :
    geometryRowsJson100.getObjVal? "physical_volume" = .ok (.str geometryRow100_physicalVolumeText) := by rfl

theorem geometryRow100_physicalVolume_numerator_no_slash :
    geometryRow100_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow100_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow100_physicalVolumeNumeratorChars = some (360516992179449709901465825119672936748653097 : Int) := by decide +kernel

theorem geometryRow100_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow100_physicalVolumeDenominatorChars = some (1523624120460490309632000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow100_physicalVolume_denominator_nonzero : (1523624120460490309632000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow100_physicalVolume_parse :
    parseRational geometryRow100_physicalVolumeText = .ok geometryRowsTyped100.physicalVolume :=
  original_rational_fraction_of_chars geometryRow100_physicalVolumeNumeratorChars geometryRow100_physicalVolumeDenominatorChars
    (360516992179449709901465825119672936748653097 : Int) (1523624120460490309632000000000000000000000000000000000000000000000 : Int)
    geometryRow100_physicalVolume_numerator_no_slash geometryRow100_physicalVolume_numerator_parse
    geometryRow100_physicalVolume_denominator_parse geometryRow100_physicalVolume_denominator_nonzero

theorem geometryRow100_physicalVolume_read :
    rationalField geometryRowsJson100 "physical_volume" = .ok geometryRowsTyped100.physicalVolume :=
  original_rationalField_of_string geometryRowsJson100 "physical_volume" geometryRow100_physicalVolumeText
    geometryRowsTyped100.physicalVolume geometryRow100_physicalVolume_field geometryRow100_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_physicalVolume_complete"
  err.flush

noncomputable def geometryRow100_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow100_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow100_meanGapText : String := String.ofList (geometryRow100_meanGapNumeratorChars ++ '/' :: geometryRow100_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_meanGap_before_field"
  err.flush

theorem geometryRow100_meanGap_field :
    geometryRowsJson100.getObjVal? "mean_gap" = .ok (.str geometryRow100_meanGapText) := by rfl

theorem geometryRow100_meanGap_numerator_no_slash :
    geometryRow100_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow100_meanGap_numerator_parse :
    SourceJson.intChars geometryRow100_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow100_meanGap_denominator_parse :
    SourceJson.intChars geometryRow100_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow100_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow100_meanGap_parse :
    parseRational geometryRow100_meanGapText = .ok geometryRowsTyped100.meanGap :=
  original_rational_fraction_of_chars geometryRow100_meanGapNumeratorChars geometryRow100_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow100_meanGap_numerator_no_slash geometryRow100_meanGap_numerator_parse
    geometryRow100_meanGap_denominator_parse geometryRow100_meanGap_denominator_nonzero

theorem geometryRow100_meanGap_read :
    rationalField geometryRowsJson100 "mean_gap" = .ok geometryRowsTyped100.meanGap :=
  original_rationalField_of_string geometryRowsJson100 "mean_gap" geometryRow100_meanGapText
    geometryRowsTyped100.meanGap geometryRow100_meanGap_field geometryRow100_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_meanGap_complete"
  err.flush

noncomputable def geometryRow100_jensenBoundNumeratorChars : List Char := ['2', '1', '8', '6', '6', '8', '4', '8', '2', '4', '2', '2', '2', '0', '5', '1', '1', '4', '6', '7', '6', '5', '1', '7', '9', '1', '2', '6', '9', '3', '6', '9', '9', '6', '0', '1', '4', '1', '4', '3', '5', '0', '5', '8', '8', '7', '5', '8', '2', '5', '3', '1', '8', '1', '5', '1', '0', '1', '2', '6', '8', '0', '0', '9', '3', '4', '9', '1', '6', '3', '0', '2', '9', '4', '9', '9', '0', '5', '1', '0', '3', '7', '8', '5', '0', '9', '5', '2', '1', '4', '8', '4', '3', '7', '5', '0', '0']
noncomputable def geometryRow100_jensenBoundDenominatorChars : List Char := ['1', '3', '3', '1', '8', '4', '6', '7', '1', '2', '4', '9', '2', '7', '3', '9', '2', '7', '6', '3', '3', '5', '4', '2', '3', '7', '8', '8', '3', '7', '8', '7', '0', '4', '5', '5', '1', '3', '0', '9', '2', '6', '9', '0', '7', '6', '7', '3', '0', '8', '4', '5', '9', '5', '5', '7', '0', '1', '9', '4', '8', '3', '8', '2', '5', '8', '4', '1', '4', '0', '5', '3', '2', '0', '6', '4', '6', '2', '6', '5', '8', '7', '5', '8', '0', '4', '5', '8', '2', '8', '0', '3', '4', '8', '9', '4', '0', '8', '8', '6', '6', '8', '8', '4', '7', '9', '9', '9', '2', '7']
noncomputable def geometryRow100_jensenBoundText : String := String.ofList (geometryRow100_jensenBoundNumeratorChars ++ '/' :: geometryRow100_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_jensenBound_before_field"
  err.flush

theorem geometryRow100_jensenBound_field :
    geometryRowsJson100.getObjVal? "jensen_bound" = .ok (.str geometryRow100_jensenBoundText) := by rfl

theorem geometryRow100_jensenBound_numerator_no_slash :
    geometryRow100_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow100_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow100_jensenBoundNumeratorChars = some (2186684824222051146765179126936996014143505887582531815101268009349163029499051037850952148437500 : Int) := by decide +kernel

theorem geometryRow100_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow100_jensenBoundDenominatorChars = some (13318467124927392763354237883787045513092690767308459557019483825841405320646265875804582803489408866884799927 : Int) := by decide +kernel

theorem geometryRow100_jensenBound_denominator_nonzero : (13318467124927392763354237883787045513092690767308459557019483825841405320646265875804582803489408866884799927 : Int) ≠ 0 := by decide +kernel

theorem geometryRow100_jensenBound_parse :
    parseRational geometryRow100_jensenBoundText = .ok geometryRowsTyped100.jensenBound :=
  original_rational_fraction_of_chars geometryRow100_jensenBoundNumeratorChars geometryRow100_jensenBoundDenominatorChars
    (2186684824222051146765179126936996014143505887582531815101268009349163029499051037850952148437500 : Int) (13318467124927392763354237883787045513092690767308459557019483825841405320646265875804582803489408866884799927 : Int)
    geometryRow100_jensenBound_numerator_no_slash geometryRow100_jensenBound_numerator_parse
    geometryRow100_jensenBound_denominator_parse geometryRow100_jensenBound_denominator_nonzero

theorem geometryRow100_jensenBound_read :
    rationalField geometryRowsJson100 "jensen_bound" = .ok geometryRowsTyped100.jensenBound :=
  original_rationalField_of_string geometryRowsJson100 "jensen_bound" geometryRow100_jensenBoundText
    geometryRowsTyped100.jensenBound geometryRow100_jensenBound_field geometryRow100_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_factorMaxima_before"
  err.flush

theorem geometryRow100_factorMaxima_read :
    rationalArrayField geometryRowsJson100 "factor_maxima" = .ok geometryRowsTyped100.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_gapWeightedMeans_before"
  err.flush

theorem geometryRow100_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson100 "gap_weighted_means" = .ok geometryRowsTyped100.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow100_floorChars : List Char := ['1', '3', '0', '0', '8', '0', '3', '0', '0', '5', '2', '9', '9', '9', '4', '1', '3']
noncomputable def geometryRow100_floorText : String := String.ofList geometryRow100_floorChars

theorem geometryRow100_floor_text_read :
    geometryRowsJson100.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow100_floorText := by rfl

theorem geometryRow100_floor_chars_parse :
    SourceJson.intChars geometryRow100_floorChars = some (13008030052999413 : Int) := by decide +kernel

theorem geometryRow100_floor_parse :
    parseInteger geometryRow100_floorText = .ok geometryRowsTyped100.jensenFloorQ96 := by
  simp only [geometryRow100_floorText, parseInteger, String.toList_ofList, geometryRow100_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_100 :
    decodeGeometryRow geometryRowsJson100 = .ok geometryRowsTyped100 :=
  original_geometryRow_of_fields geometryRowsJson100 geometryRowsTyped100 geometryRow100_floorText
    geometryRow100_simplexId_read geometryRow100_vertexIds_read
    geometryRow100_physicalVolume_read geometryRow100_meanGap_read
    geometryRow100_factorMaxima_read geometryRow100_gapWeightedMeans_read
    geometryRow100_jensenBound_read geometryRow100_floor_text_read geometryRow100_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_100_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson101 : SourceJson :=
  (SimplicesBlock051.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped101 : GeometryRow :=
  { simplexId := 101,
    vertexIds := #[39, 37, 24, 23, 19, 18, 15, 14, 7],
    physicalVolume := ((152715842539569449884390845877051132856285813 : ℚ) / (5332684421611716083712000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((403117 : ℚ) / (7200000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((143027519999 : ℚ) / (1901520000000 : ℚ)), ((28688790439 : ℚ) / (380304000000 : ℚ)), ((841423359493 : ℚ) / (5704560000000 : ℚ)), ((39950182681 : ℚ) / (369740000000 : ℚ)), ((407219092051 : ℚ) / (7986384000000 : ℚ)), ((268989216623 : ℚ) / (5704560000000 : ℚ)), ((90975794179 : ℚ) / (2101680000000 : ℚ)), ((1707217740157 : ℚ) / (39931920000000 : ℚ)), ((1696551241279 : ℚ) / (39931920000000 : ℚ)), ((63716552119 : ℚ) / (1597276800000 : ℚ))],
    jensenBound := ((4242858964433786793344268995381826636194936311153575425350383925440857724079104000000000000000 : ℚ) / (207606917151965459775173527074837683738248226834447869523845660921306384903624866613922842425761165835004271 : ℚ)),
    jensenFloorQ96 := (1619184582916393 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_simplexId_before"
  err.flush

theorem geometryRow101_simplexId_read :
    geometryRowsJson101.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped101.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_vertexIds_before"
  err.flush

theorem geometryRow101_vertexIds_read :
    geometryRowsJson101.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped101.vertexIds := by decide +kernel

noncomputable def geometryRow101_physicalVolumeNumeratorChars : List Char := ['1', '5', '2', '7', '1', '5', '8', '4', '2', '5', '3', '9', '5', '6', '9', '4', '4', '9', '8', '8', '4', '3', '9', '0', '8', '4', '5', '8', '7', '7', '0', '5', '1', '1', '3', '2', '8', '5', '6', '2', '8', '5', '8', '1', '3']
noncomputable def geometryRow101_physicalVolumeDenominatorChars : List Char := ['5', '3', '3', '2', '6', '8', '4', '4', '2', '1', '6', '1', '1', '7', '1', '6', '0', '8', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow101_physicalVolumeText : String := String.ofList (geometryRow101_physicalVolumeNumeratorChars ++ '/' :: geometryRow101_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_physicalVolume_before_field"
  err.flush

theorem geometryRow101_physicalVolume_field :
    geometryRowsJson101.getObjVal? "physical_volume" = .ok (.str geometryRow101_physicalVolumeText) := by rfl

theorem geometryRow101_physicalVolume_numerator_no_slash :
    geometryRow101_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow101_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow101_physicalVolumeNumeratorChars = some (152715842539569449884390845877051132856285813 : Int) := by decide +kernel

theorem geometryRow101_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow101_physicalVolumeDenominatorChars = some (5332684421611716083712000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow101_physicalVolume_denominator_nonzero : (5332684421611716083712000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow101_physicalVolume_parse :
    parseRational geometryRow101_physicalVolumeText = .ok geometryRowsTyped101.physicalVolume :=
  original_rational_fraction_of_chars geometryRow101_physicalVolumeNumeratorChars geometryRow101_physicalVolumeDenominatorChars
    (152715842539569449884390845877051132856285813 : Int) (5332684421611716083712000000000000000000000000000000000000000000000 : Int)
    geometryRow101_physicalVolume_numerator_no_slash geometryRow101_physicalVolume_numerator_parse
    geometryRow101_physicalVolume_denominator_parse geometryRow101_physicalVolume_denominator_nonzero

theorem geometryRow101_physicalVolume_read :
    rationalField geometryRowsJson101 "physical_volume" = .ok geometryRowsTyped101.physicalVolume :=
  original_rationalField_of_string geometryRowsJson101 "physical_volume" geometryRow101_physicalVolumeText
    geometryRowsTyped101.physicalVolume geometryRow101_physicalVolume_field geometryRow101_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_physicalVolume_complete"
  err.flush

noncomputable def geometryRow101_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow101_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow101_meanGapText : String := String.ofList (geometryRow101_meanGapNumeratorChars ++ '/' :: geometryRow101_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_meanGap_before_field"
  err.flush

theorem geometryRow101_meanGap_field :
    geometryRowsJson101.getObjVal? "mean_gap" = .ok (.str geometryRow101_meanGapText) := by rfl

theorem geometryRow101_meanGap_numerator_no_slash :
    geometryRow101_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow101_meanGap_numerator_parse :
    SourceJson.intChars geometryRow101_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow101_meanGap_denominator_parse :
    SourceJson.intChars geometryRow101_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow101_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow101_meanGap_parse :
    parseRational geometryRow101_meanGapText = .ok geometryRowsTyped101.meanGap :=
  original_rational_fraction_of_chars geometryRow101_meanGapNumeratorChars geometryRow101_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow101_meanGap_numerator_no_slash geometryRow101_meanGap_numerator_parse
    geometryRow101_meanGap_denominator_parse geometryRow101_meanGap_denominator_nonzero

theorem geometryRow101_meanGap_read :
    rationalField geometryRowsJson101 "mean_gap" = .ok geometryRowsTyped101.meanGap :=
  original_rationalField_of_string geometryRowsJson101 "mean_gap" geometryRow101_meanGapText
    geometryRowsTyped101.meanGap geometryRow101_meanGap_field geometryRow101_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_meanGap_complete"
  err.flush

noncomputable def geometryRow101_jensenBoundNumeratorChars : List Char := ['4', '2', '4', '2', '8', '5', '8', '9', '6', '4', '4', '3', '3', '7', '8', '6', '7', '9', '3', '3', '4', '4', '2', '6', '8', '9', '9', '5', '3', '8', '1', '8', '2', '6', '6', '3', '6', '1', '9', '4', '9', '3', '6', '3', '1', '1', '1', '5', '3', '5', '7', '5', '4', '2', '5', '3', '5', '0', '3', '8', '3', '9', '2', '5', '4', '4', '0', '8', '5', '7', '7', '2', '4', '0', '7', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow101_jensenBoundDenominatorChars : List Char := ['2', '0', '7', '6', '0', '6', '9', '1', '7', '1', '5', '1', '9', '6', '5', '4', '5', '9', '7', '7', '5', '1', '7', '3', '5', '2', '7', '0', '7', '4', '8', '3', '7', '6', '8', '3', '7', '3', '8', '2', '4', '8', '2', '2', '6', '8', '3', '4', '4', '4', '7', '8', '6', '9', '5', '2', '3', '8', '4', '5', '6', '6', '0', '9', '2', '1', '3', '0', '6', '3', '8', '4', '9', '0', '3', '6', '2', '4', '8', '6', '6', '6', '1', '3', '9', '2', '2', '8', '4', '2', '4', '2', '5', '7', '6', '1', '1', '6', '5', '8', '3', '5', '0', '0', '4', '2', '7', '1']
noncomputable def geometryRow101_jensenBoundText : String := String.ofList (geometryRow101_jensenBoundNumeratorChars ++ '/' :: geometryRow101_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_jensenBound_before_field"
  err.flush

theorem geometryRow101_jensenBound_field :
    geometryRowsJson101.getObjVal? "jensen_bound" = .ok (.str geometryRow101_jensenBoundText) := by rfl

theorem geometryRow101_jensenBound_numerator_no_slash :
    geometryRow101_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow101_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow101_jensenBoundNumeratorChars = some (4242858964433786793344268995381826636194936311153575425350383925440857724079104000000000000000 : Int) := by decide +kernel

theorem geometryRow101_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow101_jensenBoundDenominatorChars = some (207606917151965459775173527074837683738248226834447869523845660921306384903624866613922842425761165835004271 : Int) := by decide +kernel

theorem geometryRow101_jensenBound_denominator_nonzero : (207606917151965459775173527074837683738248226834447869523845660921306384903624866613922842425761165835004271 : Int) ≠ 0 := by decide +kernel

theorem geometryRow101_jensenBound_parse :
    parseRational geometryRow101_jensenBoundText = .ok geometryRowsTyped101.jensenBound :=
  original_rational_fraction_of_chars geometryRow101_jensenBoundNumeratorChars geometryRow101_jensenBoundDenominatorChars
    (4242858964433786793344268995381826636194936311153575425350383925440857724079104000000000000000 : Int) (207606917151965459775173527074837683738248226834447869523845660921306384903624866613922842425761165835004271 : Int)
    geometryRow101_jensenBound_numerator_no_slash geometryRow101_jensenBound_numerator_parse
    geometryRow101_jensenBound_denominator_parse geometryRow101_jensenBound_denominator_nonzero

theorem geometryRow101_jensenBound_read :
    rationalField geometryRowsJson101 "jensen_bound" = .ok geometryRowsTyped101.jensenBound :=
  original_rationalField_of_string geometryRowsJson101 "jensen_bound" geometryRow101_jensenBoundText
    geometryRowsTyped101.jensenBound geometryRow101_jensenBound_field geometryRow101_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_factorMaxima_before"
  err.flush

theorem geometryRow101_factorMaxima_read :
    rationalArrayField geometryRowsJson101 "factor_maxima" = .ok geometryRowsTyped101.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_gapWeightedMeans_before"
  err.flush

theorem geometryRow101_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson101 "gap_weighted_means" = .ok geometryRowsTyped101.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow101_floorChars : List Char := ['1', '6', '1', '9', '1', '8', '4', '5', '8', '2', '9', '1', '6', '3', '9', '3']
noncomputable def geometryRow101_floorText : String := String.ofList geometryRow101_floorChars

theorem geometryRow101_floor_text_read :
    geometryRowsJson101.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow101_floorText := by rfl

theorem geometryRow101_floor_chars_parse :
    SourceJson.intChars geometryRow101_floorChars = some (1619184582916393 : Int) := by decide +kernel

theorem geometryRow101_floor_parse :
    parseInteger geometryRow101_floorText = .ok geometryRowsTyped101.jensenFloorQ96 := by
  simp only [geometryRow101_floorText, parseInteger, String.toList_ofList, geometryRow101_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_101 :
    decodeGeometryRow geometryRowsJson101 = .ok geometryRowsTyped101 :=
  original_geometryRow_of_fields geometryRowsJson101 geometryRowsTyped101 geometryRow101_floorText
    geometryRow101_simplexId_read geometryRow101_vertexIds_read
    geometryRow101_physicalVolume_read geometryRow101_meanGap_read
    geometryRow101_factorMaxima_read geometryRow101_gapWeightedMeans_read
    geometryRow101_jensenBound_read geometryRow101_floor_text_read geometryRow101_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_101_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock051 : List SourceJson := [geometryRowsJson100, geometryRowsJson101]
noncomputable def geometryRowsTypedBlock051 : List (GeometryRow) := [geometryRowsTyped100, geometryRowsTyped101]
noncomputable def geometryRowsTypedThroughBlock051 : List (GeometryRow) := geometryRowsTypedThroughBlock050 ++ geometryRowsTypedBlock051

theorem geometry_Rows_block_051_push_eq (acc : List SourceJson) :
    SimplicesBlock051.blockPush acc = [geometryRowsJson101, geometryRowsJson100] ++ acc := by rfl

theorem geometry_Rows_block_051_reverse (acc : List SourceJson) :
    (SimplicesBlock051.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock051 := by
  rw [geometry_Rows_block_051_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_051 :
    geometryRowsJsonBlock051.mapM decodeGeometryRow = .ok geometryRowsTypedBlock051 := by
  simp only [geometryRowsJsonBlock051, geometryRowsTypedBlock051, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_100, decode_geometry_Rows_101]
  rfl

theorem decode_geometry_Rows_through_block_051 :
    SimplicesValue.arrayAcc052.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock051 := by
  change (SimplicesBlock051.blockPush SimplicesValue.arrayAcc051).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_051_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_050, decode_geometry_Rows_block_051]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_051_complete"
  err.flush

#print axioms geometryRow100_simplexId_read
#print axioms geometryRow100_vertexIds_read
#print axioms geometryRow100_physicalVolume_field
#print axioms geometryRow100_physicalVolume_numerator_no_slash
#print axioms geometryRow100_physicalVolume_numerator_parse
#print axioms geometryRow100_physicalVolume_denominator_parse
#print axioms geometryRow100_physicalVolume_denominator_nonzero
#print axioms geometryRow100_physicalVolume_parse
#print axioms geometryRow100_physicalVolume_read
#print axioms geometryRow100_meanGap_field
#print axioms geometryRow100_meanGap_numerator_no_slash
#print axioms geometryRow100_meanGap_numerator_parse
#print axioms geometryRow100_meanGap_denominator_parse
#print axioms geometryRow100_meanGap_denominator_nonzero
#print axioms geometryRow100_meanGap_parse
#print axioms geometryRow100_meanGap_read
#print axioms geometryRow100_jensenBound_field
#print axioms geometryRow100_jensenBound_numerator_no_slash
#print axioms geometryRow100_jensenBound_numerator_parse
#print axioms geometryRow100_jensenBound_denominator_parse
#print axioms geometryRow100_jensenBound_denominator_nonzero
#print axioms geometryRow100_jensenBound_parse
#print axioms geometryRow100_jensenBound_read
#print axioms geometryRow100_factorMaxima_read
#print axioms geometryRow100_gapWeightedMeans_read
#print axioms geometryRow100_floor_text_read
#print axioms geometryRow100_floor_chars_parse
#print axioms geometryRow100_floor_parse
#print axioms decode_geometry_Rows_100
#print axioms geometryRow101_simplexId_read
#print axioms geometryRow101_vertexIds_read
#print axioms geometryRow101_physicalVolume_field
#print axioms geometryRow101_physicalVolume_numerator_no_slash
#print axioms geometryRow101_physicalVolume_numerator_parse
#print axioms geometryRow101_physicalVolume_denominator_parse
#print axioms geometryRow101_physicalVolume_denominator_nonzero
#print axioms geometryRow101_physicalVolume_parse
#print axioms geometryRow101_physicalVolume_read
#print axioms geometryRow101_meanGap_field
#print axioms geometryRow101_meanGap_numerator_no_slash
#print axioms geometryRow101_meanGap_numerator_parse
#print axioms geometryRow101_meanGap_denominator_parse
#print axioms geometryRow101_meanGap_denominator_nonzero
#print axioms geometryRow101_meanGap_parse
#print axioms geometryRow101_meanGap_read
#print axioms geometryRow101_jensenBound_field
#print axioms geometryRow101_jensenBound_numerator_no_slash
#print axioms geometryRow101_jensenBound_numerator_parse
#print axioms geometryRow101_jensenBound_denominator_parse
#print axioms geometryRow101_jensenBound_denominator_nonzero
#print axioms geometryRow101_jensenBound_parse
#print axioms geometryRow101_jensenBound_read
#print axioms geometryRow101_factorMaxima_read
#print axioms geometryRow101_gapWeightedMeans_read
#print axioms geometryRow101_floor_text_read
#print axioms geometryRow101_floor_chars_parse
#print axioms geometryRow101_floor_parse
#print axioms decode_geometry_Rows_101
#print axioms geometry_Rows_block_051_push_eq
#print axioms geometry_Rows_block_051_reverse
#print axioms decode_geometry_Rows_block_051
#print axioms decode_geometry_Rows_through_block_051

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
