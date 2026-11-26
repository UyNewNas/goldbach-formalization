import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows002

/-! Original simplices typed block 3, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson006 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped006 : GeometryRow :=
  { simplexId := 6,
    vertexIds := #[39, 35, 29, 28, 25, 8, 3, 1, 0],
    physicalVolume := ((33407500981952803839618577801251361 : ℚ) / (25669140480000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((84373 : ℚ) / (2080000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((31804741548751 : ℚ) / (363854400000000 : ℚ)), ((32172540558511 : ℚ) / (363854400000000 : ℚ)), ((862447000631 : ℚ) / (5997600000000 : ℚ)), ((41528671339553 : ℚ) / (363854400000000 : ℚ)), ((613409022259 : ℚ) / (9172800000000 : ℚ)), ((26333141693539 : ℚ) / (545781600000000 : ℚ)), ((23159366856271 : ℚ) / (623750400000000 : ℚ)), ((21865213749661 : ℚ) / (623750400000000 : ℚ)), ((34588535593783 : ℚ) / (1091563200000000 : ℚ)), ((34588317281143 : ℚ) / (1091563200000000 : ℚ))],
    jensenBound := ((67593623384897093376598782123733111199432799430163465577672071938612342627777844328640020480000000000000000000000000 : ℚ) / (12366720262112950222920136351718079235427286337826574853421726124754850703193854221812821968682674314961353083524682559806785202593 : ℚ)),
    jensenFloorQ96 := (433042752238305 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_simplexId_before"
  err.flush

theorem geometryRow006_simplexId_read :
    geometryRowsJson006.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped006.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_vertexIds_before"
  err.flush

theorem geometryRow006_vertexIds_read :
    geometryRowsJson006.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped006.vertexIds := by decide +kernel

noncomputable def geometryRow006_physicalVolumeNumeratorChars : List Char := ['3', '3', '4', '0', '7', '5', '0', '0', '9', '8', '1', '9', '5', '2', '8', '0', '3', '8', '3', '9', '6', '1', '8', '5', '7', '7', '8', '0', '1', '2', '5', '1', '3', '6', '1']
noncomputable def geometryRow006_physicalVolumeDenominatorChars : List Char := ['2', '5', '6', '6', '9', '1', '4', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_physicalVolumeText : String := String.ofList (geometryRow006_physicalVolumeNumeratorChars ++ '/' :: geometryRow006_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_physicalVolume_before_field"
  err.flush

theorem geometryRow006_physicalVolume_field :
    geometryRowsJson006.getObjVal? "physical_volume" = .ok (.str geometryRow006_physicalVolumeText) := by rfl

theorem geometryRow006_physicalVolume_numerator_no_slash :
    geometryRow006_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow006_physicalVolumeNumeratorChars = some (33407500981952803839618577801251361 : Int) := by decide +kernel

theorem geometryRow006_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow006_physicalVolumeDenominatorChars = some (25669140480000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow006_physicalVolume_denominator_nonzero : (25669140480000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_physicalVolume_parse :
    parseRational geometryRow006_physicalVolumeText = .ok geometryRowsTyped006.physicalVolume :=
  original_rational_fraction_of_chars geometryRow006_physicalVolumeNumeratorChars geometryRow006_physicalVolumeDenominatorChars
    (33407500981952803839618577801251361 : Int) (25669140480000000000000000000000000000000000000000000000000 : Int)
    geometryRow006_physicalVolume_numerator_no_slash geometryRow006_physicalVolume_numerator_parse
    geometryRow006_physicalVolume_denominator_parse geometryRow006_physicalVolume_denominator_nonzero

theorem geometryRow006_physicalVolume_read :
    rationalField geometryRowsJson006 "physical_volume" = .ok geometryRowsTyped006.physicalVolume :=
  original_rationalField_of_string geometryRowsJson006 "physical_volume" geometryRow006_physicalVolumeText
    geometryRowsTyped006.physicalVolume geometryRow006_physicalVolume_field geometryRow006_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_physicalVolume_complete"
  err.flush

noncomputable def geometryRow006_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow006_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_meanGapText : String := String.ofList (geometryRow006_meanGapNumeratorChars ++ '/' :: geometryRow006_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_meanGap_before_field"
  err.flush

theorem geometryRow006_meanGap_field :
    geometryRowsJson006.getObjVal? "mean_gap" = .ok (.str geometryRow006_meanGapText) := by rfl

theorem geometryRow006_meanGap_numerator_no_slash :
    geometryRow006_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_meanGap_numerator_parse :
    SourceJson.intChars geometryRow006_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow006_meanGap_denominator_parse :
    SourceJson.intChars geometryRow006_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow006_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_meanGap_parse :
    parseRational geometryRow006_meanGapText = .ok geometryRowsTyped006.meanGap :=
  original_rational_fraction_of_chars geometryRow006_meanGapNumeratorChars geometryRow006_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow006_meanGap_numerator_no_slash geometryRow006_meanGap_numerator_parse
    geometryRow006_meanGap_denominator_parse geometryRow006_meanGap_denominator_nonzero

theorem geometryRow006_meanGap_read :
    rationalField geometryRowsJson006 "mean_gap" = .ok geometryRowsTyped006.meanGap :=
  original_rationalField_of_string geometryRowsJson006 "mean_gap" geometryRow006_meanGapText
    geometryRowsTyped006.meanGap geometryRow006_meanGap_field geometryRow006_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_meanGap_complete"
  err.flush

noncomputable def geometryRow006_jensenBoundNumeratorChars : List Char := ['6', '7', '5', '9', '3', '6', '2', '3', '3', '8', '4', '8', '9', '7', '0', '9', '3', '3', '7', '6', '5', '9', '8', '7', '8', '2', '1', '2', '3', '7', '3', '3', '1', '1', '1', '1', '9', '9', '4', '3', '2', '7', '9', '9', '4', '3', '0', '1', '6', '3', '4', '6', '5', '5', '7', '7', '6', '7', '2', '0', '7', '1', '9', '3', '8', '6', '1', '2', '3', '4', '2', '6', '2', '7', '7', '7', '7', '8', '4', '4', '3', '2', '8', '6', '4', '0', '0', '2', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_jensenBoundDenominatorChars : List Char := ['1', '2', '3', '6', '6', '7', '2', '0', '2', '6', '2', '1', '1', '2', '9', '5', '0', '2', '2', '2', '9', '2', '0', '1', '3', '6', '3', '5', '1', '7', '1', '8', '0', '7', '9', '2', '3', '5', '4', '2', '7', '2', '8', '6', '3', '3', '7', '8', '2', '6', '5', '7', '4', '8', '5', '3', '4', '2', '1', '7', '2', '6', '1', '2', '4', '7', '5', '4', '8', '5', '0', '7', '0', '3', '1', '9', '3', '8', '5', '4', '2', '2', '1', '8', '1', '2', '8', '2', '1', '9', '6', '8', '6', '8', '2', '6', '7', '4', '3', '1', '4', '9', '6', '1', '3', '5', '3', '0', '8', '3', '5', '2', '4', '6', '8', '2', '5', '5', '9', '8', '0', '6', '7', '8', '5', '2', '0', '2', '5', '9', '3']
noncomputable def geometryRow006_jensenBoundText : String := String.ofList (geometryRow006_jensenBoundNumeratorChars ++ '/' :: geometryRow006_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_jensenBound_before_field"
  err.flush

theorem geometryRow006_jensenBound_field :
    geometryRowsJson006.getObjVal? "jensen_bound" = .ok (.str geometryRow006_jensenBoundText) := by rfl

theorem geometryRow006_jensenBound_numerator_no_slash :
    geometryRow006_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow006_jensenBoundNumeratorChars = some (67593623384897093376598782123733111199432799430163465577672071938612342627777844328640020480000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow006_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow006_jensenBoundDenominatorChars = some (12366720262112950222920136351718079235427286337826574853421726124754850703193854221812821968682674314961353083524682559806785202593 : Int) := by decide +kernel

theorem geometryRow006_jensenBound_denominator_nonzero : (12366720262112950222920136351718079235427286337826574853421726124754850703193854221812821968682674314961353083524682559806785202593 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_jensenBound_parse :
    parseRational geometryRow006_jensenBoundText = .ok geometryRowsTyped006.jensenBound :=
  original_rational_fraction_of_chars geometryRow006_jensenBoundNumeratorChars geometryRow006_jensenBoundDenominatorChars
    (67593623384897093376598782123733111199432799430163465577672071938612342627777844328640020480000000000000000000000000 : Int) (12366720262112950222920136351718079235427286337826574853421726124754850703193854221812821968682674314961353083524682559806785202593 : Int)
    geometryRow006_jensenBound_numerator_no_slash geometryRow006_jensenBound_numerator_parse
    geometryRow006_jensenBound_denominator_parse geometryRow006_jensenBound_denominator_nonzero

theorem geometryRow006_jensenBound_read :
    rationalField geometryRowsJson006 "jensen_bound" = .ok geometryRowsTyped006.jensenBound :=
  original_rationalField_of_string geometryRowsJson006 "jensen_bound" geometryRow006_jensenBoundText
    geometryRowsTyped006.jensenBound geometryRow006_jensenBound_field geometryRow006_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_factorMaxima_before"
  err.flush

theorem geometryRow006_factorMaxima_read :
    rationalArrayField geometryRowsJson006 "factor_maxima" = .ok geometryRowsTyped006.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_gapWeightedMeans_before"
  err.flush

theorem geometryRow006_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson006 "gap_weighted_means" = .ok geometryRowsTyped006.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow006_floorChars : List Char := ['4', '3', '3', '0', '4', '2', '7', '5', '2', '2', '3', '8', '3', '0', '5']
noncomputable def geometryRow006_floorText : String := String.ofList geometryRow006_floorChars

theorem geometryRow006_floor_text_read :
    geometryRowsJson006.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow006_floorText := by rfl

theorem geometryRow006_floor_chars_parse :
    SourceJson.intChars geometryRow006_floorChars = some (433042752238305 : Int) := by decide +kernel

theorem geometryRow006_floor_parse :
    parseInteger geometryRow006_floorText = .ok geometryRowsTyped006.jensenFloorQ96 := by
  simp only [geometryRow006_floorText, parseInteger, String.toList_ofList, geometryRow006_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_006 :
    decodeGeometryRow geometryRowsJson006 = .ok geometryRowsTyped006 :=
  original_geometryRow_of_fields geometryRowsJson006 geometryRowsTyped006 geometryRow006_floorText
    geometryRow006_simplexId_read geometryRow006_vertexIds_read
    geometryRow006_physicalVolume_read geometryRow006_meanGap_read
    geometryRow006_factorMaxima_read geometryRow006_gapWeightedMeans_read
    geometryRow006_jensenBound_read geometryRow006_floor_text_read geometryRow006_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_006_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson007 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped007 : GeometryRow :=
  { simplexId := 7,
    vertexIds := #[39, 35, 29, 28, 25, 8, 3, 2, 0],
    physicalVolume := ((2532233288904484339739201825498880014927729 : ℚ) / (369789637754880000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1074023 : ℚ) / (937125000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((84373 : ℚ) / (2080000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2102259700626433553 : ℚ) / (24424249640700000000 : ℚ)), ((17120433867455199829 : ℚ) / (195393997125600000000 : ℚ)), ((1856047071606655871 : ℚ) / (12883120689600000000 : ℚ)), ((45231811965204726709 : ℚ) / (390787994251200000000 : ℚ)), ((82460635781158549 : ℚ) / (1231474771800000000 : ℚ)), ((54990789114350949919 : ℚ) / (1172363982753600000000 : ℚ)), ((3562053651883269059 : ℚ) / (95703182265600000000 : ℚ)), ((3363489337308898769 : ℚ) / (95703182265600000000 : ℚ)), ((146315074830819959 : ℚ) / (4579546807631250000 : ℚ)), ((18417733748940894097 : ℚ) / (586181991376800000000 : ℚ))],
    jensenBound := ((1574949232342798467615518438642496335548604344279930360972006427400395527342129943428658074663111497879080315176043485344583998707249714539301670577920000000000000000000000000 : ℚ) / (26021815236585303226428635947942460502152423531949903687566789066919424081615705901997113081588581357065561638399306146773133761635071875288238670444173945221875714956684719796100339617 : ℚ)),
    jensenFloorQ96 := (4795220187265664527 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_simplexId_before"
  err.flush

theorem geometryRow007_simplexId_read :
    geometryRowsJson007.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped007.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_vertexIds_before"
  err.flush

theorem geometryRow007_vertexIds_read :
    geometryRowsJson007.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped007.vertexIds := by decide +kernel

noncomputable def geometryRow007_physicalVolumeNumeratorChars : List Char := ['2', '5', '3', '2', '2', '3', '3', '2', '8', '8', '9', '0', '4', '4', '8', '4', '3', '3', '9', '7', '3', '9', '2', '0', '1', '8', '2', '5', '4', '9', '8', '8', '8', '0', '0', '1', '4', '9', '2', '7', '7', '2', '9']
noncomputable def geometryRow007_physicalVolumeDenominatorChars : List Char := ['3', '6', '9', '7', '8', '9', '6', '3', '7', '7', '5', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_physicalVolumeText : String := String.ofList (geometryRow007_physicalVolumeNumeratorChars ++ '/' :: geometryRow007_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_physicalVolume_before_field"
  err.flush

theorem geometryRow007_physicalVolume_field :
    geometryRowsJson007.getObjVal? "physical_volume" = .ok (.str geometryRow007_physicalVolumeText) := by rfl

theorem geometryRow007_physicalVolume_numerator_no_slash :
    geometryRow007_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow007_physicalVolumeNumeratorChars = some (2532233288904484339739201825498880014927729 : Int) := by decide +kernel

theorem geometryRow007_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow007_physicalVolumeDenominatorChars = some (369789637754880000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow007_physicalVolume_denominator_nonzero : (369789637754880000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_physicalVolume_parse :
    parseRational geometryRow007_physicalVolumeText = .ok geometryRowsTyped007.physicalVolume :=
  original_rational_fraction_of_chars geometryRow007_physicalVolumeNumeratorChars geometryRow007_physicalVolumeDenominatorChars
    (2532233288904484339739201825498880014927729 : Int) (369789637754880000000000000000000000000000000000000000000000000 : Int)
    geometryRow007_physicalVolume_numerator_no_slash geometryRow007_physicalVolume_numerator_parse
    geometryRow007_physicalVolume_denominator_parse geometryRow007_physicalVolume_denominator_nonzero

theorem geometryRow007_physicalVolume_read :
    rationalField geometryRowsJson007 "physical_volume" = .ok geometryRowsTyped007.physicalVolume :=
  original_rationalField_of_string geometryRowsJson007 "physical_volume" geometryRow007_physicalVolumeText
    geometryRowsTyped007.physicalVolume geometryRow007_physicalVolume_field geometryRow007_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_physicalVolume_complete"
  err.flush

noncomputable def geometryRow007_meanGapNumeratorChars : List Char := ['1', '0', '7', '4', '0', '2', '3']
noncomputable def geometryRow007_meanGapDenominatorChars : List Char := ['9', '3', '7', '1', '2', '5', '0', '0', '0']
noncomputable def geometryRow007_meanGapText : String := String.ofList (geometryRow007_meanGapNumeratorChars ++ '/' :: geometryRow007_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_meanGap_before_field"
  err.flush

theorem geometryRow007_meanGap_field :
    geometryRowsJson007.getObjVal? "mean_gap" = .ok (.str geometryRow007_meanGapText) := by rfl

theorem geometryRow007_meanGap_numerator_no_slash :
    geometryRow007_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_meanGap_numerator_parse :
    SourceJson.intChars geometryRow007_meanGapNumeratorChars = some (1074023 : Int) := by decide +kernel

theorem geometryRow007_meanGap_denominator_parse :
    SourceJson.intChars geometryRow007_meanGapDenominatorChars = some (937125000 : Int) := by decide +kernel

theorem geometryRow007_meanGap_denominator_nonzero : (937125000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_meanGap_parse :
    parseRational geometryRow007_meanGapText = .ok geometryRowsTyped007.meanGap :=
  original_rational_fraction_of_chars geometryRow007_meanGapNumeratorChars geometryRow007_meanGapDenominatorChars
    (1074023 : Int) (937125000 : Int)
    geometryRow007_meanGap_numerator_no_slash geometryRow007_meanGap_numerator_parse
    geometryRow007_meanGap_denominator_parse geometryRow007_meanGap_denominator_nonzero

theorem geometryRow007_meanGap_read :
    rationalField geometryRowsJson007 "mean_gap" = .ok geometryRowsTyped007.meanGap :=
  original_rationalField_of_string geometryRowsJson007 "mean_gap" geometryRow007_meanGapText
    geometryRowsTyped007.meanGap geometryRow007_meanGap_field geometryRow007_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_meanGap_complete"
  err.flush

noncomputable def geometryRow007_jensenBoundNumeratorChars : List Char := ['1', '5', '7', '4', '9', '4', '9', '2', '3', '2', '3', '4', '2', '7', '9', '8', '4', '6', '7', '6', '1', '5', '5', '1', '8', '4', '3', '8', '6', '4', '2', '4', '9', '6', '3', '3', '5', '5', '4', '8', '6', '0', '4', '3', '4', '4', '2', '7', '9', '9', '3', '0', '3', '6', '0', '9', '7', '2', '0', '0', '6', '4', '2', '7', '4', '0', '0', '3', '9', '5', '5', '2', '7', '3', '4', '2', '1', '2', '9', '9', '4', '3', '4', '2', '8', '6', '5', '8', '0', '7', '4', '6', '6', '3', '1', '1', '1', '4', '9', '7', '8', '7', '9', '0', '8', '0', '3', '1', '5', '1', '7', '6', '0', '4', '3', '4', '8', '5', '3', '4', '4', '5', '8', '3', '9', '9', '8', '7', '0', '7', '2', '4', '9', '7', '1', '4', '5', '3', '9', '3', '0', '1', '6', '7', '0', '5', '7', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_jensenBoundDenominatorChars : List Char := ['2', '6', '0', '2', '1', '8', '1', '5', '2', '3', '6', '5', '8', '5', '3', '0', '3', '2', '2', '6', '4', '2', '8', '6', '3', '5', '9', '4', '7', '9', '4', '2', '4', '6', '0', '5', '0', '2', '1', '5', '2', '4', '2', '3', '5', '3', '1', '9', '4', '9', '9', '0', '3', '6', '8', '7', '5', '6', '6', '7', '8', '9', '0', '6', '6', '9', '1', '9', '4', '2', '4', '0', '8', '1', '6', '1', '5', '7', '0', '5', '9', '0', '1', '9', '9', '7', '1', '1', '3', '0', '8', '1', '5', '8', '8', '5', '8', '1', '3', '5', '7', '0', '6', '5', '5', '6', '1', '6', '3', '8', '3', '9', '9', '3', '0', '6', '1', '4', '6', '7', '7', '3', '1', '3', '3', '7', '6', '1', '6', '3', '5', '0', '7', '1', '8', '7', '5', '2', '8', '8', '2', '3', '8', '6', '7', '0', '4', '4', '4', '1', '7', '3', '9', '4', '5', '2', '2', '1', '8', '7', '5', '7', '1', '4', '9', '5', '6', '6', '8', '4', '7', '1', '9', '7', '9', '6', '1', '0', '0', '3', '3', '9', '6', '1', '7']
noncomputable def geometryRow007_jensenBoundText : String := String.ofList (geometryRow007_jensenBoundNumeratorChars ++ '/' :: geometryRow007_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_jensenBound_before_field"
  err.flush

theorem geometryRow007_jensenBound_field :
    geometryRowsJson007.getObjVal? "jensen_bound" = .ok (.str geometryRow007_jensenBoundText) := by rfl

theorem geometryRow007_jensenBound_numerator_no_slash :
    geometryRow007_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow007_jensenBoundNumeratorChars = some (1574949232342798467615518438642496335548604344279930360972006427400395527342129943428658074663111497879080315176043485344583998707249714539301670577920000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow007_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow007_jensenBoundDenominatorChars = some (26021815236585303226428635947942460502152423531949903687566789066919424081615705901997113081588581357065561638399306146773133761635071875288238670444173945221875714956684719796100339617 : Int) := by decide +kernel

theorem geometryRow007_jensenBound_denominator_nonzero : (26021815236585303226428635947942460502152423531949903687566789066919424081615705901997113081588581357065561638399306146773133761635071875288238670444173945221875714956684719796100339617 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_jensenBound_parse :
    parseRational geometryRow007_jensenBoundText = .ok geometryRowsTyped007.jensenBound :=
  original_rational_fraction_of_chars geometryRow007_jensenBoundNumeratorChars geometryRow007_jensenBoundDenominatorChars
    (1574949232342798467615518438642496335548604344279930360972006427400395527342129943428658074663111497879080315176043485344583998707249714539301670577920000000000000000000000000 : Int) (26021815236585303226428635947942460502152423531949903687566789066919424081615705901997113081588581357065561638399306146773133761635071875288238670444173945221875714956684719796100339617 : Int)
    geometryRow007_jensenBound_numerator_no_slash geometryRow007_jensenBound_numerator_parse
    geometryRow007_jensenBound_denominator_parse geometryRow007_jensenBound_denominator_nonzero

theorem geometryRow007_jensenBound_read :
    rationalField geometryRowsJson007 "jensen_bound" = .ok geometryRowsTyped007.jensenBound :=
  original_rationalField_of_string geometryRowsJson007 "jensen_bound" geometryRow007_jensenBoundText
    geometryRowsTyped007.jensenBound geometryRow007_jensenBound_field geometryRow007_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_factorMaxima_before"
  err.flush

theorem geometryRow007_factorMaxima_read :
    rationalArrayField geometryRowsJson007 "factor_maxima" = .ok geometryRowsTyped007.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_gapWeightedMeans_before"
  err.flush

theorem geometryRow007_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson007 "gap_weighted_means" = .ok geometryRowsTyped007.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow007_floorChars : List Char := ['4', '7', '9', '5', '2', '2', '0', '1', '8', '7', '2', '6', '5', '6', '6', '4', '5', '2', '7']
noncomputable def geometryRow007_floorText : String := String.ofList geometryRow007_floorChars

theorem geometryRow007_floor_text_read :
    geometryRowsJson007.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow007_floorText := by rfl

theorem geometryRow007_floor_chars_parse :
    SourceJson.intChars geometryRow007_floorChars = some (4795220187265664527 : Int) := by decide +kernel

theorem geometryRow007_floor_parse :
    parseInteger geometryRow007_floorText = .ok geometryRowsTyped007.jensenFloorQ96 := by
  simp only [geometryRow007_floorText, parseInteger, String.toList_ofList, geometryRow007_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_007 :
    decodeGeometryRow geometryRowsJson007 = .ok geometryRowsTyped007 :=
  original_geometryRow_of_fields geometryRowsJson007 geometryRowsTyped007 geometryRow007_floorText
    geometryRow007_simplexId_read geometryRow007_vertexIds_read
    geometryRow007_physicalVolume_read geometryRow007_meanGap_read
    geometryRow007_factorMaxima_read geometryRow007_gapWeightedMeans_read
    geometryRow007_jensenBound_read geometryRow007_floor_text_read geometryRow007_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_007_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock003 : List SourceJson := [geometryRowsJson006, geometryRowsJson007]
noncomputable def geometryRowsTypedBlock003 : List (GeometryRow) := [geometryRowsTyped006, geometryRowsTyped007]
noncomputable def geometryRowsTypedThroughBlock003 : List (GeometryRow) := geometryRowsTypedThroughBlock002 ++ geometryRowsTypedBlock003

theorem geometry_Rows_block_003_push_eq (acc : List SourceJson) :
    SimplicesBlock003.blockPush acc = [geometryRowsJson007, geometryRowsJson006] ++ acc := by rfl

theorem geometry_Rows_block_003_reverse (acc : List SourceJson) :
    (SimplicesBlock003.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock003 := by
  rw [geometry_Rows_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_003 :
    geometryRowsJsonBlock003.mapM decodeGeometryRow = .ok geometryRowsTypedBlock003 := by
  simp only [geometryRowsJsonBlock003, geometryRowsTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_006, decode_geometry_Rows_007]
  rfl

theorem decode_geometry_Rows_through_block_003 :
    SimplicesValue.arrayAcc004.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock003 := by
  change (SimplicesBlock003.blockPush SimplicesValue.arrayAcc003).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_003_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_002, decode_geometry_Rows_block_003]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_003_complete"
  err.flush

#print axioms geometryRow006_simplexId_read
#print axioms geometryRow006_vertexIds_read
#print axioms geometryRow006_physicalVolume_field
#print axioms geometryRow006_physicalVolume_numerator_no_slash
#print axioms geometryRow006_physicalVolume_numerator_parse
#print axioms geometryRow006_physicalVolume_denominator_parse
#print axioms geometryRow006_physicalVolume_denominator_nonzero
#print axioms geometryRow006_physicalVolume_parse
#print axioms geometryRow006_physicalVolume_read
#print axioms geometryRow006_meanGap_field
#print axioms geometryRow006_meanGap_numerator_no_slash
#print axioms geometryRow006_meanGap_numerator_parse
#print axioms geometryRow006_meanGap_denominator_parse
#print axioms geometryRow006_meanGap_denominator_nonzero
#print axioms geometryRow006_meanGap_parse
#print axioms geometryRow006_meanGap_read
#print axioms geometryRow006_jensenBound_field
#print axioms geometryRow006_jensenBound_numerator_no_slash
#print axioms geometryRow006_jensenBound_numerator_parse
#print axioms geometryRow006_jensenBound_denominator_parse
#print axioms geometryRow006_jensenBound_denominator_nonzero
#print axioms geometryRow006_jensenBound_parse
#print axioms geometryRow006_jensenBound_read
#print axioms geometryRow006_factorMaxima_read
#print axioms geometryRow006_gapWeightedMeans_read
#print axioms geometryRow006_floor_text_read
#print axioms geometryRow006_floor_chars_parse
#print axioms geometryRow006_floor_parse
#print axioms decode_geometry_Rows_006
#print axioms geometryRow007_simplexId_read
#print axioms geometryRow007_vertexIds_read
#print axioms geometryRow007_physicalVolume_field
#print axioms geometryRow007_physicalVolume_numerator_no_slash
#print axioms geometryRow007_physicalVolume_numerator_parse
#print axioms geometryRow007_physicalVolume_denominator_parse
#print axioms geometryRow007_physicalVolume_denominator_nonzero
#print axioms geometryRow007_physicalVolume_parse
#print axioms geometryRow007_physicalVolume_read
#print axioms geometryRow007_meanGap_field
#print axioms geometryRow007_meanGap_numerator_no_slash
#print axioms geometryRow007_meanGap_numerator_parse
#print axioms geometryRow007_meanGap_denominator_parse
#print axioms geometryRow007_meanGap_denominator_nonzero
#print axioms geometryRow007_meanGap_parse
#print axioms geometryRow007_meanGap_read
#print axioms geometryRow007_jensenBound_field
#print axioms geometryRow007_jensenBound_numerator_no_slash
#print axioms geometryRow007_jensenBound_numerator_parse
#print axioms geometryRow007_jensenBound_denominator_parse
#print axioms geometryRow007_jensenBound_denominator_nonzero
#print axioms geometryRow007_jensenBound_parse
#print axioms geometryRow007_jensenBound_read
#print axioms geometryRow007_factorMaxima_read
#print axioms geometryRow007_gapWeightedMeans_read
#print axioms geometryRow007_floor_text_read
#print axioms geometryRow007_floor_chars_parse
#print axioms geometryRow007_floor_parse
#print axioms decode_geometry_Rows_007
#print axioms geometry_Rows_block_003_push_eq
#print axioms geometry_Rows_block_003_reverse
#print axioms decode_geometry_Rows_block_003
#print axioms decode_geometry_Rows_through_block_003

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
