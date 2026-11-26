import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows013

/-! Original simplices typed block 14, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson028 : SourceJson :=
  (SimplicesBlock014.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped028 : GeometryRow :=
  { simplexId := 28,
    vertexIds := #[39, 35, 29, 27, 26, 7, 6, 2, 0],
    physicalVolume := ((144376044164081813594901932275987325521 : ℚ) / (59479031808000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546639 : ℚ) / (96000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2787229763 : ℚ) / (33600000000 : ℚ)), ((19758064181 : ℚ) / (235200000000 : ℚ)), ((10191954169 : ℚ) / (70560000000 : ℚ)), ((82086035693 : ℚ) / (705600000000 : ℚ)), ((46873510127 : ℚ) / (705600000000 : ℚ)), ((16943577403 : ℚ) / (352800000000 : ℚ)), ((13656933587 : ℚ) / (352800000000 : ℚ)), ((24385904269 : ℚ) / (705600000000 : ℚ)), ((24385857229 : ℚ) / (705600000000 : ℚ)), ((21319652237 : ℚ) / (705600000000 : ℚ))],
    jensenBound := ((68891288027700187625564955515700130316359246991989325154699769282560000000000000000000000 : ℚ) / (6335584679511291354061803178867925321363672294881515073449683123206538260491362546540647144438955808889 : ℚ)),
    jensenFloorQ96 := (861503782172894 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_simplexId_before"
  err.flush

theorem geometryRow028_simplexId_read :
    geometryRowsJson028.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped028.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_vertexIds_before"
  err.flush

theorem geometryRow028_vertexIds_read :
    geometryRowsJson028.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped028.vertexIds := by decide +kernel

noncomputable def geometryRow028_physicalVolumeNumeratorChars : List Char := ['1', '4', '4', '3', '7', '6', '0', '4', '4', '1', '6', '4', '0', '8', '1', '8', '1', '3', '5', '9', '4', '9', '0', '1', '9', '3', '2', '2', '7', '5', '9', '8', '7', '3', '2', '5', '5', '2', '1']
noncomputable def geometryRow028_physicalVolumeDenominatorChars : List Char := ['5', '9', '4', '7', '9', '0', '3', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_physicalVolumeText : String := String.ofList (geometryRow028_physicalVolumeNumeratorChars ++ '/' :: geometryRow028_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_physicalVolume_before_field"
  err.flush

theorem geometryRow028_physicalVolume_field :
    geometryRowsJson028.getObjVal? "physical_volume" = .ok (.str geometryRow028_physicalVolumeText) := by rfl

theorem geometryRow028_physicalVolume_numerator_no_slash :
    geometryRow028_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow028_physicalVolumeNumeratorChars = some (144376044164081813594901932275987325521 : Int) := by decide +kernel

theorem geometryRow028_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow028_physicalVolumeDenominatorChars = some (59479031808000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow028_physicalVolume_denominator_nonzero : (59479031808000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_physicalVolume_parse :
    parseRational geometryRow028_physicalVolumeText = .ok geometryRowsTyped028.physicalVolume :=
  original_rational_fraction_of_chars geometryRow028_physicalVolumeNumeratorChars geometryRow028_physicalVolumeDenominatorChars
    (144376044164081813594901932275987325521 : Int) (59479031808000000000000000000000000000000000000000000000000000 : Int)
    geometryRow028_physicalVolume_numerator_no_slash geometryRow028_physicalVolume_numerator_parse
    geometryRow028_physicalVolume_denominator_parse geometryRow028_physicalVolume_denominator_nonzero

theorem geometryRow028_physicalVolume_read :
    rationalField geometryRowsJson028 "physical_volume" = .ok geometryRowsTyped028.physicalVolume :=
  original_rationalField_of_string geometryRowsJson028 "physical_volume" geometryRow028_physicalVolumeText
    geometryRowsTyped028.physicalVolume geometryRow028_physicalVolume_field geometryRow028_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_physicalVolume_complete"
  err.flush

noncomputable def geometryRow028_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow028_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_meanGapText : String := String.ofList (geometryRow028_meanGapNumeratorChars ++ '/' :: geometryRow028_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_meanGap_before_field"
  err.flush

theorem geometryRow028_meanGap_field :
    geometryRowsJson028.getObjVal? "mean_gap" = .ok (.str geometryRow028_meanGapText) := by rfl

theorem geometryRow028_meanGap_numerator_no_slash :
    geometryRow028_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_meanGap_numerator_parse :
    SourceJson.intChars geometryRow028_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow028_meanGap_denominator_parse :
    SourceJson.intChars geometryRow028_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow028_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_meanGap_parse :
    parseRational geometryRow028_meanGapText = .ok geometryRowsTyped028.meanGap :=
  original_rational_fraction_of_chars geometryRow028_meanGapNumeratorChars geometryRow028_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow028_meanGap_numerator_no_slash geometryRow028_meanGap_numerator_parse
    geometryRow028_meanGap_denominator_parse geometryRow028_meanGap_denominator_nonzero

theorem geometryRow028_meanGap_read :
    rationalField geometryRowsJson028 "mean_gap" = .ok geometryRowsTyped028.meanGap :=
  original_rationalField_of_string geometryRowsJson028 "mean_gap" geometryRow028_meanGapText
    geometryRowsTyped028.meanGap geometryRow028_meanGap_field geometryRow028_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_meanGap_complete"
  err.flush

noncomputable def geometryRow028_jensenBoundNumeratorChars : List Char := ['6', '8', '8', '9', '1', '2', '8', '8', '0', '2', '7', '7', '0', '0', '1', '8', '7', '6', '2', '5', '5', '6', '4', '9', '5', '5', '5', '1', '5', '7', '0', '0', '1', '3', '0', '3', '1', '6', '3', '5', '9', '2', '4', '6', '9', '9', '1', '9', '8', '9', '3', '2', '5', '1', '5', '4', '6', '9', '9', '7', '6', '9', '2', '8', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_jensenBoundDenominatorChars : List Char := ['6', '3', '3', '5', '5', '8', '4', '6', '7', '9', '5', '1', '1', '2', '9', '1', '3', '5', '4', '0', '6', '1', '8', '0', '3', '1', '7', '8', '8', '6', '7', '9', '2', '5', '3', '2', '1', '3', '6', '3', '6', '7', '2', '2', '9', '4', '8', '8', '1', '5', '1', '5', '0', '7', '3', '4', '4', '9', '6', '8', '3', '1', '2', '3', '2', '0', '6', '5', '3', '8', '2', '6', '0', '4', '9', '1', '3', '6', '2', '5', '4', '6', '5', '4', '0', '6', '4', '7', '1', '4', '4', '4', '3', '8', '9', '5', '5', '8', '0', '8', '8', '8', '9']
noncomputable def geometryRow028_jensenBoundText : String := String.ofList (geometryRow028_jensenBoundNumeratorChars ++ '/' :: geometryRow028_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_jensenBound_before_field"
  err.flush

theorem geometryRow028_jensenBound_field :
    geometryRowsJson028.getObjVal? "jensen_bound" = .ok (.str geometryRow028_jensenBoundText) := by rfl

theorem geometryRow028_jensenBound_numerator_no_slash :
    geometryRow028_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow028_jensenBoundNumeratorChars = some (68891288027700187625564955515700130316359246991989325154699769282560000000000000000000000 : Int) := by decide +kernel

theorem geometryRow028_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow028_jensenBoundDenominatorChars = some (6335584679511291354061803178867925321363672294881515073449683123206538260491362546540647144438955808889 : Int) := by decide +kernel

theorem geometryRow028_jensenBound_denominator_nonzero : (6335584679511291354061803178867925321363672294881515073449683123206538260491362546540647144438955808889 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_jensenBound_parse :
    parseRational geometryRow028_jensenBoundText = .ok geometryRowsTyped028.jensenBound :=
  original_rational_fraction_of_chars geometryRow028_jensenBoundNumeratorChars geometryRow028_jensenBoundDenominatorChars
    (68891288027700187625564955515700130316359246991989325154699769282560000000000000000000000 : Int) (6335584679511291354061803178867925321363672294881515073449683123206538260491362546540647144438955808889 : Int)
    geometryRow028_jensenBound_numerator_no_slash geometryRow028_jensenBound_numerator_parse
    geometryRow028_jensenBound_denominator_parse geometryRow028_jensenBound_denominator_nonzero

theorem geometryRow028_jensenBound_read :
    rationalField geometryRowsJson028 "jensen_bound" = .ok geometryRowsTyped028.jensenBound :=
  original_rationalField_of_string geometryRowsJson028 "jensen_bound" geometryRow028_jensenBoundText
    geometryRowsTyped028.jensenBound geometryRow028_jensenBound_field geometryRow028_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_factorMaxima_before"
  err.flush

theorem geometryRow028_factorMaxima_read :
    rationalArrayField geometryRowsJson028 "factor_maxima" = .ok geometryRowsTyped028.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_gapWeightedMeans_before"
  err.flush

theorem geometryRow028_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson028 "gap_weighted_means" = .ok geometryRowsTyped028.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow028_floorChars : List Char := ['8', '6', '1', '5', '0', '3', '7', '8', '2', '1', '7', '2', '8', '9', '4']
noncomputable def geometryRow028_floorText : String := String.ofList geometryRow028_floorChars

theorem geometryRow028_floor_text_read :
    geometryRowsJson028.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow028_floorText := by rfl

theorem geometryRow028_floor_chars_parse :
    SourceJson.intChars geometryRow028_floorChars = some (861503782172894 : Int) := by decide +kernel

theorem geometryRow028_floor_parse :
    parseInteger geometryRow028_floorText = .ok geometryRowsTyped028.jensenFloorQ96 := by
  simp only [geometryRow028_floorText, parseInteger, String.toList_ofList, geometryRow028_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_028 :
    decodeGeometryRow geometryRowsJson028 = .ok geometryRowsTyped028 :=
  original_geometryRow_of_fields geometryRowsJson028 geometryRowsTyped028 geometryRow028_floorText
    geometryRow028_simplexId_read geometryRow028_vertexIds_read
    geometryRow028_physicalVolume_read geometryRow028_meanGap_read
    geometryRow028_factorMaxima_read geometryRow028_gapWeightedMeans_read
    geometryRow028_jensenBound_read geometryRow028_floor_text_read geometryRow028_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_028_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson029 : SourceJson :=
  (SimplicesBlock014.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped029 : GeometryRow :=
  { simplexId := 29,
    vertexIds := #[39, 35, 29, 27, 9, 7, 6, 2, 0],
    physicalVolume := ((70697575387819793315252147088623081156299 : ℚ) / (22483074023424000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((9233771 : ℚ) / (168000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2848782263 : ℚ) / (33600000000 : ℚ)), ((20188931681 : ℚ) / (235200000000 : ℚ)), ((225536847 : ℚ) / (1568000000 : ℚ)), ((81227207653 : ℚ) / (705600000000 : ℚ)), ((5065191283 : ℚ) / (78400000000 : ℚ)), ((1906395297 : ℚ) / (39200000000 : ℚ)), ((1589409813 : ℚ) / (39200000000 : ℚ)), ((2661024761 : ℚ) / (78400000000 : ℚ)), ((7983058603 : ℚ) / (235200000000 : ℚ)), ((21750519737 : ℚ) / (705600000000 : ℚ))],
    jensenBound := ((302272984993947476396022521207960283065028423747739564348801024000000000000000000000 : ℚ) / (22415346115201260655067618969381190067869372887219508131120894726230517155988850058402170764222787 : ℚ)),
    jensenFloorQ96 := (1068398991284423 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_simplexId_before"
  err.flush

theorem geometryRow029_simplexId_read :
    geometryRowsJson029.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped029.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_vertexIds_before"
  err.flush

theorem geometryRow029_vertexIds_read :
    geometryRowsJson029.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped029.vertexIds := by decide +kernel

noncomputable def geometryRow029_physicalVolumeNumeratorChars : List Char := ['7', '0', '6', '9', '7', '5', '7', '5', '3', '8', '7', '8', '1', '9', '7', '9', '3', '3', '1', '5', '2', '5', '2', '1', '4', '7', '0', '8', '8', '6', '2', '3', '0', '8', '1', '1', '5', '6', '2', '9', '9']
noncomputable def geometryRow029_physicalVolumeDenominatorChars : List Char := ['2', '2', '4', '8', '3', '0', '7', '4', '0', '2', '3', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_physicalVolumeText : String := String.ofList (geometryRow029_physicalVolumeNumeratorChars ++ '/' :: geometryRow029_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_physicalVolume_before_field"
  err.flush

theorem geometryRow029_physicalVolume_field :
    geometryRowsJson029.getObjVal? "physical_volume" = .ok (.str geometryRow029_physicalVolumeText) := by rfl

theorem geometryRow029_physicalVolume_numerator_no_slash :
    geometryRow029_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow029_physicalVolumeNumeratorChars = some (70697575387819793315252147088623081156299 : Int) := by decide +kernel

theorem geometryRow029_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow029_physicalVolumeDenominatorChars = some (22483074023424000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow029_physicalVolume_denominator_nonzero : (22483074023424000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_physicalVolume_parse :
    parseRational geometryRow029_physicalVolumeText = .ok geometryRowsTyped029.physicalVolume :=
  original_rational_fraction_of_chars geometryRow029_physicalVolumeNumeratorChars geometryRow029_physicalVolumeDenominatorChars
    (70697575387819793315252147088623081156299 : Int) (22483074023424000000000000000000000000000000000000000000000000000 : Int)
    geometryRow029_physicalVolume_numerator_no_slash geometryRow029_physicalVolume_numerator_parse
    geometryRow029_physicalVolume_denominator_parse geometryRow029_physicalVolume_denominator_nonzero

theorem geometryRow029_physicalVolume_read :
    rationalField geometryRowsJson029 "physical_volume" = .ok geometryRowsTyped029.physicalVolume :=
  original_rationalField_of_string geometryRowsJson029 "physical_volume" geometryRow029_physicalVolumeText
    geometryRowsTyped029.physicalVolume geometryRow029_physicalVolume_field geometryRow029_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_physicalVolume_complete"
  err.flush

noncomputable def geometryRow029_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow029_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_meanGapText : String := String.ofList (geometryRow029_meanGapNumeratorChars ++ '/' :: geometryRow029_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_meanGap_before_field"
  err.flush

theorem geometryRow029_meanGap_field :
    geometryRowsJson029.getObjVal? "mean_gap" = .ok (.str geometryRow029_meanGapText) := by rfl

theorem geometryRow029_meanGap_numerator_no_slash :
    geometryRow029_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_meanGap_numerator_parse :
    SourceJson.intChars geometryRow029_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow029_meanGap_denominator_parse :
    SourceJson.intChars geometryRow029_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow029_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_meanGap_parse :
    parseRational geometryRow029_meanGapText = .ok geometryRowsTyped029.meanGap :=
  original_rational_fraction_of_chars geometryRow029_meanGapNumeratorChars geometryRow029_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow029_meanGap_numerator_no_slash geometryRow029_meanGap_numerator_parse
    geometryRow029_meanGap_denominator_parse geometryRow029_meanGap_denominator_nonzero

theorem geometryRow029_meanGap_read :
    rationalField geometryRowsJson029 "mean_gap" = .ok geometryRowsTyped029.meanGap :=
  original_rationalField_of_string geometryRowsJson029 "mean_gap" geometryRow029_meanGapText
    geometryRowsTyped029.meanGap geometryRow029_meanGap_field geometryRow029_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_meanGap_complete"
  err.flush

noncomputable def geometryRow029_jensenBoundNumeratorChars : List Char := ['3', '0', '2', '2', '7', '2', '9', '8', '4', '9', '9', '3', '9', '4', '7', '4', '7', '6', '3', '9', '6', '0', '2', '2', '5', '2', '1', '2', '0', '7', '9', '6', '0', '2', '8', '3', '0', '6', '5', '0', '2', '8', '4', '2', '3', '7', '4', '7', '7', '3', '9', '5', '6', '4', '3', '4', '8', '8', '0', '1', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_jensenBoundDenominatorChars : List Char := ['2', '2', '4', '1', '5', '3', '4', '6', '1', '1', '5', '2', '0', '1', '2', '6', '0', '6', '5', '5', '0', '6', '7', '6', '1', '8', '9', '6', '9', '3', '8', '1', '1', '9', '0', '0', '6', '7', '8', '6', '9', '3', '7', '2', '8', '8', '7', '2', '1', '9', '5', '0', '8', '1', '3', '1', '1', '2', '0', '8', '9', '4', '7', '2', '6', '2', '3', '0', '5', '1', '7', '1', '5', '5', '9', '8', '8', '8', '5', '0', '0', '5', '8', '4', '0', '2', '1', '7', '0', '7', '6', '4', '2', '2', '2', '7', '8', '7']
noncomputable def geometryRow029_jensenBoundText : String := String.ofList (geometryRow029_jensenBoundNumeratorChars ++ '/' :: geometryRow029_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_jensenBound_before_field"
  err.flush

theorem geometryRow029_jensenBound_field :
    geometryRowsJson029.getObjVal? "jensen_bound" = .ok (.str geometryRow029_jensenBoundText) := by rfl

theorem geometryRow029_jensenBound_numerator_no_slash :
    geometryRow029_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow029_jensenBoundNumeratorChars = some (302272984993947476396022521207960283065028423747739564348801024000000000000000000000 : Int) := by decide +kernel

theorem geometryRow029_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow029_jensenBoundDenominatorChars = some (22415346115201260655067618969381190067869372887219508131120894726230517155988850058402170764222787 : Int) := by decide +kernel

theorem geometryRow029_jensenBound_denominator_nonzero : (22415346115201260655067618969381190067869372887219508131120894726230517155988850058402170764222787 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_jensenBound_parse :
    parseRational geometryRow029_jensenBoundText = .ok geometryRowsTyped029.jensenBound :=
  original_rational_fraction_of_chars geometryRow029_jensenBoundNumeratorChars geometryRow029_jensenBoundDenominatorChars
    (302272984993947476396022521207960283065028423747739564348801024000000000000000000000 : Int) (22415346115201260655067618969381190067869372887219508131120894726230517155988850058402170764222787 : Int)
    geometryRow029_jensenBound_numerator_no_slash geometryRow029_jensenBound_numerator_parse
    geometryRow029_jensenBound_denominator_parse geometryRow029_jensenBound_denominator_nonzero

theorem geometryRow029_jensenBound_read :
    rationalField geometryRowsJson029 "jensen_bound" = .ok geometryRowsTyped029.jensenBound :=
  original_rationalField_of_string geometryRowsJson029 "jensen_bound" geometryRow029_jensenBoundText
    geometryRowsTyped029.jensenBound geometryRow029_jensenBound_field geometryRow029_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_factorMaxima_before"
  err.flush

theorem geometryRow029_factorMaxima_read :
    rationalArrayField geometryRowsJson029 "factor_maxima" = .ok geometryRowsTyped029.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_gapWeightedMeans_before"
  err.flush

theorem geometryRow029_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson029 "gap_weighted_means" = .ok geometryRowsTyped029.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow029_floorChars : List Char := ['1', '0', '6', '8', '3', '9', '8', '9', '9', '1', '2', '8', '4', '4', '2', '3']
noncomputable def geometryRow029_floorText : String := String.ofList geometryRow029_floorChars

theorem geometryRow029_floor_text_read :
    geometryRowsJson029.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow029_floorText := by rfl

theorem geometryRow029_floor_chars_parse :
    SourceJson.intChars geometryRow029_floorChars = some (1068398991284423 : Int) := by decide +kernel

theorem geometryRow029_floor_parse :
    parseInteger geometryRow029_floorText = .ok geometryRowsTyped029.jensenFloorQ96 := by
  simp only [geometryRow029_floorText, parseInteger, String.toList_ofList, geometryRow029_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_029 :
    decodeGeometryRow geometryRowsJson029 = .ok geometryRowsTyped029 :=
  original_geometryRow_of_fields geometryRowsJson029 geometryRowsTyped029 geometryRow029_floorText
    geometryRow029_simplexId_read geometryRow029_vertexIds_read
    geometryRow029_physicalVolume_read geometryRow029_meanGap_read
    geometryRow029_factorMaxima_read geometryRow029_gapWeightedMeans_read
    geometryRow029_jensenBound_read geometryRow029_floor_text_read geometryRow029_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_029_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock014 : List SourceJson := [geometryRowsJson028, geometryRowsJson029]
noncomputable def geometryRowsTypedBlock014 : List (GeometryRow) := [geometryRowsTyped028, geometryRowsTyped029]
noncomputable def geometryRowsTypedThroughBlock014 : List (GeometryRow) := geometryRowsTypedThroughBlock013 ++ geometryRowsTypedBlock014

theorem geometry_Rows_block_014_push_eq (acc : List SourceJson) :
    SimplicesBlock014.blockPush acc = [geometryRowsJson029, geometryRowsJson028] ++ acc := by rfl

theorem geometry_Rows_block_014_reverse (acc : List SourceJson) :
    (SimplicesBlock014.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock014 := by
  rw [geometry_Rows_block_014_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_014 :
    geometryRowsJsonBlock014.mapM decodeGeometryRow = .ok geometryRowsTypedBlock014 := by
  simp only [geometryRowsJsonBlock014, geometryRowsTypedBlock014, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_028, decode_geometry_Rows_029]
  rfl

theorem decode_geometry_Rows_through_block_014 :
    SimplicesValue.arrayAcc015.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock014 := by
  change (SimplicesBlock014.blockPush SimplicesValue.arrayAcc014).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_014_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_013, decode_geometry_Rows_block_014]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_014_complete"
  err.flush

#print axioms geometryRow028_simplexId_read
#print axioms geometryRow028_vertexIds_read
#print axioms geometryRow028_physicalVolume_field
#print axioms geometryRow028_physicalVolume_numerator_no_slash
#print axioms geometryRow028_physicalVolume_numerator_parse
#print axioms geometryRow028_physicalVolume_denominator_parse
#print axioms geometryRow028_physicalVolume_denominator_nonzero
#print axioms geometryRow028_physicalVolume_parse
#print axioms geometryRow028_physicalVolume_read
#print axioms geometryRow028_meanGap_field
#print axioms geometryRow028_meanGap_numerator_no_slash
#print axioms geometryRow028_meanGap_numerator_parse
#print axioms geometryRow028_meanGap_denominator_parse
#print axioms geometryRow028_meanGap_denominator_nonzero
#print axioms geometryRow028_meanGap_parse
#print axioms geometryRow028_meanGap_read
#print axioms geometryRow028_jensenBound_field
#print axioms geometryRow028_jensenBound_numerator_no_slash
#print axioms geometryRow028_jensenBound_numerator_parse
#print axioms geometryRow028_jensenBound_denominator_parse
#print axioms geometryRow028_jensenBound_denominator_nonzero
#print axioms geometryRow028_jensenBound_parse
#print axioms geometryRow028_jensenBound_read
#print axioms geometryRow028_factorMaxima_read
#print axioms geometryRow028_gapWeightedMeans_read
#print axioms geometryRow028_floor_text_read
#print axioms geometryRow028_floor_chars_parse
#print axioms geometryRow028_floor_parse
#print axioms decode_geometry_Rows_028
#print axioms geometryRow029_simplexId_read
#print axioms geometryRow029_vertexIds_read
#print axioms geometryRow029_physicalVolume_field
#print axioms geometryRow029_physicalVolume_numerator_no_slash
#print axioms geometryRow029_physicalVolume_numerator_parse
#print axioms geometryRow029_physicalVolume_denominator_parse
#print axioms geometryRow029_physicalVolume_denominator_nonzero
#print axioms geometryRow029_physicalVolume_parse
#print axioms geometryRow029_physicalVolume_read
#print axioms geometryRow029_meanGap_field
#print axioms geometryRow029_meanGap_numerator_no_slash
#print axioms geometryRow029_meanGap_numerator_parse
#print axioms geometryRow029_meanGap_denominator_parse
#print axioms geometryRow029_meanGap_denominator_nonzero
#print axioms geometryRow029_meanGap_parse
#print axioms geometryRow029_meanGap_read
#print axioms geometryRow029_jensenBound_field
#print axioms geometryRow029_jensenBound_numerator_no_slash
#print axioms geometryRow029_jensenBound_numerator_parse
#print axioms geometryRow029_jensenBound_denominator_parse
#print axioms geometryRow029_jensenBound_denominator_nonzero
#print axioms geometryRow029_jensenBound_parse
#print axioms geometryRow029_jensenBound_read
#print axioms geometryRow029_factorMaxima_read
#print axioms geometryRow029_gapWeightedMeans_read
#print axioms geometryRow029_floor_text_read
#print axioms geometryRow029_floor_chars_parse
#print axioms geometryRow029_floor_parse
#print axioms decode_geometry_Rows_029
#print axioms geometry_Rows_block_014_push_eq
#print axioms geometry_Rows_block_014_reverse
#print axioms decode_geometry_Rows_block_014
#print axioms decode_geometry_Rows_through_block_014

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
