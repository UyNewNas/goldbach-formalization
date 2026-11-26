import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows070

/-! Original simplices typed block 71, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson140 : SourceJson :=
  (SimplicesBlock071.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped140 : GeometryRow :=
  { simplexId := 140,
    vertexIds := #[39, 33, 31, 24, 23, 21, 19, 18, 15],
    physicalVolume := ((22638867735580705679010490534816325609076041 : ℚ) / (5139033397005312000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1921543 : ℚ) / (30000000 : ℚ)), ((1115573 : ℚ) / (21600000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((13431708952171 : ℚ) / (195500025000000 : ℚ)), ((53898093549289 : ℚ) / (782000100000000 : ℚ)), ((4815667681519 : ℚ) / (32583337500000 : ℚ)), ((98345452440619 : ℚ) / (938400120000000 : ℚ)), ((1100356783643 : ℚ) / (20853336000000 : ℚ)), ((1218058393129 : ℚ) / (26066670000000 : ℚ)), ((1384341414719 : ℚ) / (30868425000000 : ℚ)), ((103957259500559 : ℚ) / (2346000300000000 : ℚ)), ((205850643311641 : ℚ) / (4692000600000000 : ℚ)), ((203793360824101 : ℚ) / (4692000600000000 : ℚ))],
    jensenBound := ((8684826450055700757814258248166443834965284985182722816339115536411358086001731763187670018761402788212890625000000000 : ℚ) / (2774325390281572393252425896087433948842247118347861446020341283256413502150665773387206035568835522015114574659845222884055320018553 : ℚ)),
    jensenFloorQ96 := (248018074521301 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_simplexId_before"
  err.flush

theorem geometryRow140_simplexId_read :
    geometryRowsJson140.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped140.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_vertexIds_before"
  err.flush

theorem geometryRow140_vertexIds_read :
    geometryRowsJson140.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped140.vertexIds := by decide +kernel

noncomputable def geometryRow140_physicalVolumeNumeratorChars : List Char := ['2', '2', '6', '3', '8', '8', '6', '7', '7', '3', '5', '5', '8', '0', '7', '0', '5', '6', '7', '9', '0', '1', '0', '4', '9', '0', '5', '3', '4', '8', '1', '6', '3', '2', '5', '6', '0', '9', '0', '7', '6', '0', '4', '1']
noncomputable def geometryRow140_physicalVolumeDenominatorChars : List Char := ['5', '1', '3', '9', '0', '3', '3', '3', '9', '7', '0', '0', '5', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow140_physicalVolumeText : String := String.ofList (geometryRow140_physicalVolumeNumeratorChars ++ '/' :: geometryRow140_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_physicalVolume_before_field"
  err.flush

theorem geometryRow140_physicalVolume_field :
    geometryRowsJson140.getObjVal? "physical_volume" = .ok (.str geometryRow140_physicalVolumeText) := by rfl

theorem geometryRow140_physicalVolume_numerator_no_slash :
    geometryRow140_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow140_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow140_physicalVolumeNumeratorChars = some (22638867735580705679010490534816325609076041 : Int) := by decide +kernel

theorem geometryRow140_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow140_physicalVolumeDenominatorChars = some (5139033397005312000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow140_physicalVolume_denominator_nonzero : (5139033397005312000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow140_physicalVolume_parse :
    parseRational geometryRow140_physicalVolumeText = .ok geometryRowsTyped140.physicalVolume :=
  original_rational_fraction_of_chars geometryRow140_physicalVolumeNumeratorChars geometryRow140_physicalVolumeDenominatorChars
    (22638867735580705679010490534816325609076041 : Int) (5139033397005312000000000000000000000000000000000000000000000000000 : Int)
    geometryRow140_physicalVolume_numerator_no_slash geometryRow140_physicalVolume_numerator_parse
    geometryRow140_physicalVolume_denominator_parse geometryRow140_physicalVolume_denominator_nonzero

theorem geometryRow140_physicalVolume_read :
    rationalField geometryRowsJson140 "physical_volume" = .ok geometryRowsTyped140.physicalVolume :=
  original_rationalField_of_string geometryRowsJson140 "physical_volume" geometryRow140_physicalVolumeText
    geometryRowsTyped140.physicalVolume geometryRow140_physicalVolume_field geometryRow140_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_physicalVolume_complete"
  err.flush

noncomputable def geometryRow140_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow140_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow140_meanGapText : String := String.ofList (geometryRow140_meanGapNumeratorChars ++ '/' :: geometryRow140_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_meanGap_before_field"
  err.flush

theorem geometryRow140_meanGap_field :
    geometryRowsJson140.getObjVal? "mean_gap" = .ok (.str geometryRow140_meanGapText) := by rfl

theorem geometryRow140_meanGap_numerator_no_slash :
    geometryRow140_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow140_meanGap_numerator_parse :
    SourceJson.intChars geometryRow140_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow140_meanGap_denominator_parse :
    SourceJson.intChars geometryRow140_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow140_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow140_meanGap_parse :
    parseRational geometryRow140_meanGapText = .ok geometryRowsTyped140.meanGap :=
  original_rational_fraction_of_chars geometryRow140_meanGapNumeratorChars geometryRow140_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow140_meanGap_numerator_no_slash geometryRow140_meanGap_numerator_parse
    geometryRow140_meanGap_denominator_parse geometryRow140_meanGap_denominator_nonzero

theorem geometryRow140_meanGap_read :
    rationalField geometryRowsJson140 "mean_gap" = .ok geometryRowsTyped140.meanGap :=
  original_rationalField_of_string geometryRowsJson140 "mean_gap" geometryRow140_meanGapText
    geometryRowsTyped140.meanGap geometryRow140_meanGap_field geometryRow140_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_meanGap_complete"
  err.flush

noncomputable def geometryRow140_jensenBoundNumeratorChars : List Char := ['8', '6', '8', '4', '8', '2', '6', '4', '5', '0', '0', '5', '5', '7', '0', '0', '7', '5', '7', '8', '1', '4', '2', '5', '8', '2', '4', '8', '1', '6', '6', '4', '4', '3', '8', '3', '4', '9', '6', '5', '2', '8', '4', '9', '8', '5', '1', '8', '2', '7', '2', '2', '8', '1', '6', '3', '3', '9', '1', '1', '5', '5', '3', '6', '4', '1', '1', '3', '5', '8', '0', '8', '6', '0', '0', '1', '7', '3', '1', '7', '6', '3', '1', '8', '7', '6', '7', '0', '0', '1', '8', '7', '6', '1', '4', '0', '2', '7', '8', '8', '2', '1', '2', '8', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow140_jensenBoundDenominatorChars : List Char := ['2', '7', '7', '4', '3', '2', '5', '3', '9', '0', '2', '8', '1', '5', '7', '2', '3', '9', '3', '2', '5', '2', '4', '2', '5', '8', '9', '6', '0', '8', '7', '4', '3', '3', '9', '4', '8', '8', '4', '2', '2', '4', '7', '1', '1', '8', '3', '4', '7', '8', '6', '1', '4', '4', '6', '0', '2', '0', '3', '4', '1', '2', '8', '3', '2', '5', '6', '4', '1', '3', '5', '0', '2', '1', '5', '0', '6', '6', '5', '7', '7', '3', '3', '8', '7', '2', '0', '6', '0', '3', '5', '5', '6', '8', '8', '3', '5', '5', '2', '2', '0', '1', '5', '1', '1', '4', '5', '7', '4', '6', '5', '9', '8', '4', '5', '2', '2', '2', '8', '8', '4', '0', '5', '5', '3', '2', '0', '0', '1', '8', '5', '5', '3']
noncomputable def geometryRow140_jensenBoundText : String := String.ofList (geometryRow140_jensenBoundNumeratorChars ++ '/' :: geometryRow140_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_jensenBound_before_field"
  err.flush

theorem geometryRow140_jensenBound_field :
    geometryRowsJson140.getObjVal? "jensen_bound" = .ok (.str geometryRow140_jensenBoundText) := by rfl

theorem geometryRow140_jensenBound_numerator_no_slash :
    geometryRow140_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow140_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow140_jensenBoundNumeratorChars = some (8684826450055700757814258248166443834965284985182722816339115536411358086001731763187670018761402788212890625000000000 : Int) := by decide +kernel

theorem geometryRow140_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow140_jensenBoundDenominatorChars = some (2774325390281572393252425896087433948842247118347861446020341283256413502150665773387206035568835522015114574659845222884055320018553 : Int) := by decide +kernel

theorem geometryRow140_jensenBound_denominator_nonzero : (2774325390281572393252425896087433948842247118347861446020341283256413502150665773387206035568835522015114574659845222884055320018553 : Int) ≠ 0 := by decide +kernel

theorem geometryRow140_jensenBound_parse :
    parseRational geometryRow140_jensenBoundText = .ok geometryRowsTyped140.jensenBound :=
  original_rational_fraction_of_chars geometryRow140_jensenBoundNumeratorChars geometryRow140_jensenBoundDenominatorChars
    (8684826450055700757814258248166443834965284985182722816339115536411358086001731763187670018761402788212890625000000000 : Int) (2774325390281572393252425896087433948842247118347861446020341283256413502150665773387206035568835522015114574659845222884055320018553 : Int)
    geometryRow140_jensenBound_numerator_no_slash geometryRow140_jensenBound_numerator_parse
    geometryRow140_jensenBound_denominator_parse geometryRow140_jensenBound_denominator_nonzero

theorem geometryRow140_jensenBound_read :
    rationalField geometryRowsJson140 "jensen_bound" = .ok geometryRowsTyped140.jensenBound :=
  original_rationalField_of_string geometryRowsJson140 "jensen_bound" geometryRow140_jensenBoundText
    geometryRowsTyped140.jensenBound geometryRow140_jensenBound_field geometryRow140_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_factorMaxima_before"
  err.flush

theorem geometryRow140_factorMaxima_read :
    rationalArrayField geometryRowsJson140 "factor_maxima" = .ok geometryRowsTyped140.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_gapWeightedMeans_before"
  err.flush

theorem geometryRow140_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson140 "gap_weighted_means" = .ok geometryRowsTyped140.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow140_floorChars : List Char := ['2', '4', '8', '0', '1', '8', '0', '7', '4', '5', '2', '1', '3', '0', '1']
noncomputable def geometryRow140_floorText : String := String.ofList geometryRow140_floorChars

theorem geometryRow140_floor_text_read :
    geometryRowsJson140.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow140_floorText := by rfl

theorem geometryRow140_floor_chars_parse :
    SourceJson.intChars geometryRow140_floorChars = some (248018074521301 : Int) := by decide +kernel

theorem geometryRow140_floor_parse :
    parseInteger geometryRow140_floorText = .ok geometryRowsTyped140.jensenFloorQ96 := by
  simp only [geometryRow140_floorText, parseInteger, String.toList_ofList, geometryRow140_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_140 :
    decodeGeometryRow geometryRowsJson140 = .ok geometryRowsTyped140 :=
  original_geometryRow_of_fields geometryRowsJson140 geometryRowsTyped140 geometryRow140_floorText
    geometryRow140_simplexId_read geometryRow140_vertexIds_read
    geometryRow140_physicalVolume_read geometryRow140_meanGap_read
    geometryRow140_factorMaxima_read geometryRow140_gapWeightedMeans_read
    geometryRow140_jensenBound_read geometryRow140_floor_text_read geometryRow140_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_140_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson141 : SourceJson :=
  (SimplicesBlock071.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped141 : GeometryRow :=
  { simplexId := 141,
    vertexIds := #[39, 33, 31, 24, 22, 19, 18, 15, 14],
    physicalVolume := ((126514016332598906486820196877148282393811 : ℚ) / (27408945423579955200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1921543 : ℚ) / (30000000 : ℚ)), ((734331 : ℚ) / (14000000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((82135653691 : ℚ) / (1188450000000 : ℚ)), ((164791847627 : ℚ) / (2376900000000 : ℚ)), ((29230582159 : ℚ) / (198075000000 : ℚ)), ((10515247207477 : ℚ) / (99829800000000 : ℚ)), ((587280921887 : ℚ) / (11092200000000 : ℚ)), ((37301640269 : ℚ) / (792300000000 : ℚ)), ((2241829210807 : ℚ) / (49914900000000 : ℚ)), ((2188519134337 : ℚ) / (49914900000000 : ℚ)), ((2188515806677 : ℚ) / (49914900000000 : ℚ)), ((4260891240839 : ℚ) / (99829800000000 : ℚ))],
    jensenBound := ((1955775586924486970297198125649776105831531972200880929665547371470316586440293212890625000000000000 : ℚ) / (595666510099486808871532642638469313025154928865966792099946607886787220989739859944102905343608599993436471674120283 : ℚ)),
    jensenFloorQ96 := (260132982826 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_simplexId_before"
  err.flush

theorem geometryRow141_simplexId_read :
    geometryRowsJson141.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped141.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_vertexIds_before"
  err.flush

theorem geometryRow141_vertexIds_read :
    geometryRowsJson141.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped141.vertexIds := by decide +kernel

noncomputable def geometryRow141_physicalVolumeNumeratorChars : List Char := ['1', '2', '6', '5', '1', '4', '0', '1', '6', '3', '3', '2', '5', '9', '8', '9', '0', '6', '4', '8', '6', '8', '2', '0', '1', '9', '6', '8', '7', '7', '1', '4', '8', '2', '8', '2', '3', '9', '3', '8', '1', '1']
noncomputable def geometryRow141_physicalVolumeDenominatorChars : List Char := ['2', '7', '4', '0', '8', '9', '4', '5', '4', '2', '3', '5', '7', '9', '9', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow141_physicalVolumeText : String := String.ofList (geometryRow141_physicalVolumeNumeratorChars ++ '/' :: geometryRow141_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_physicalVolume_before_field"
  err.flush

theorem geometryRow141_physicalVolume_field :
    geometryRowsJson141.getObjVal? "physical_volume" = .ok (.str geometryRow141_physicalVolumeText) := by rfl

theorem geometryRow141_physicalVolume_numerator_no_slash :
    geometryRow141_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow141_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow141_physicalVolumeNumeratorChars = some (126514016332598906486820196877148282393811 : Int) := by decide +kernel

theorem geometryRow141_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow141_physicalVolumeDenominatorChars = some (27408945423579955200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow141_physicalVolume_denominator_nonzero : (27408945423579955200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow141_physicalVolume_parse :
    parseRational geometryRow141_physicalVolumeText = .ok geometryRowsTyped141.physicalVolume :=
  original_rational_fraction_of_chars geometryRow141_physicalVolumeNumeratorChars geometryRow141_physicalVolumeDenominatorChars
    (126514016332598906486820196877148282393811 : Int) (27408945423579955200000000000000000000000000000000000000000000000000 : Int)
    geometryRow141_physicalVolume_numerator_no_slash geometryRow141_physicalVolume_numerator_parse
    geometryRow141_physicalVolume_denominator_parse geometryRow141_physicalVolume_denominator_nonzero

theorem geometryRow141_physicalVolume_read :
    rationalField geometryRowsJson141 "physical_volume" = .ok geometryRowsTyped141.physicalVolume :=
  original_rationalField_of_string geometryRowsJson141 "physical_volume" geometryRow141_physicalVolumeText
    geometryRowsTyped141.physicalVolume geometryRow141_physicalVolume_field geometryRow141_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_physicalVolume_complete"
  err.flush

noncomputable def geometryRow141_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow141_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow141_meanGapText : String := String.ofList (geometryRow141_meanGapNumeratorChars ++ '/' :: geometryRow141_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_meanGap_before_field"
  err.flush

theorem geometryRow141_meanGap_field :
    geometryRowsJson141.getObjVal? "mean_gap" = .ok (.str geometryRow141_meanGapText) := by rfl

theorem geometryRow141_meanGap_numerator_no_slash :
    geometryRow141_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow141_meanGap_numerator_parse :
    SourceJson.intChars geometryRow141_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow141_meanGap_denominator_parse :
    SourceJson.intChars geometryRow141_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow141_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow141_meanGap_parse :
    parseRational geometryRow141_meanGapText = .ok geometryRowsTyped141.meanGap :=
  original_rational_fraction_of_chars geometryRow141_meanGapNumeratorChars geometryRow141_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow141_meanGap_numerator_no_slash geometryRow141_meanGap_numerator_parse
    geometryRow141_meanGap_denominator_parse geometryRow141_meanGap_denominator_nonzero

theorem geometryRow141_meanGap_read :
    rationalField geometryRowsJson141 "mean_gap" = .ok geometryRowsTyped141.meanGap :=
  original_rationalField_of_string geometryRowsJson141 "mean_gap" geometryRow141_meanGapText
    geometryRowsTyped141.meanGap geometryRow141_meanGap_field geometryRow141_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_meanGap_complete"
  err.flush

noncomputable def geometryRow141_jensenBoundNumeratorChars : List Char := ['1', '9', '5', '5', '7', '7', '5', '5', '8', '6', '9', '2', '4', '4', '8', '6', '9', '7', '0', '2', '9', '7', '1', '9', '8', '1', '2', '5', '6', '4', '9', '7', '7', '6', '1', '0', '5', '8', '3', '1', '5', '3', '1', '9', '7', '2', '2', '0', '0', '8', '8', '0', '9', '2', '9', '6', '6', '5', '5', '4', '7', '3', '7', '1', '4', '7', '0', '3', '1', '6', '5', '8', '6', '4', '4', '0', '2', '9', '3', '2', '1', '2', '8', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow141_jensenBoundDenominatorChars : List Char := ['5', '9', '5', '6', '6', '6', '5', '1', '0', '0', '9', '9', '4', '8', '6', '8', '0', '8', '8', '7', '1', '5', '3', '2', '6', '4', '2', '6', '3', '8', '4', '6', '9', '3', '1', '3', '0', '2', '5', '1', '5', '4', '9', '2', '8', '8', '6', '5', '9', '6', '6', '7', '9', '2', '0', '9', '9', '9', '4', '6', '6', '0', '7', '8', '8', '6', '7', '8', '7', '2', '2', '0', '9', '8', '9', '7', '3', '9', '8', '5', '9', '9', '4', '4', '1', '0', '2', '9', '0', '5', '3', '4', '3', '6', '0', '8', '5', '9', '9', '9', '9', '3', '4', '3', '6', '4', '7', '1', '6', '7', '4', '1', '2', '0', '2', '8', '3']
noncomputable def geometryRow141_jensenBoundText : String := String.ofList (geometryRow141_jensenBoundNumeratorChars ++ '/' :: geometryRow141_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_jensenBound_before_field"
  err.flush

theorem geometryRow141_jensenBound_field :
    geometryRowsJson141.getObjVal? "jensen_bound" = .ok (.str geometryRow141_jensenBoundText) := by rfl

theorem geometryRow141_jensenBound_numerator_no_slash :
    geometryRow141_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow141_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow141_jensenBoundNumeratorChars = some (1955775586924486970297198125649776105831531972200880929665547371470316586440293212890625000000000000 : Int) := by decide +kernel

theorem geometryRow141_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow141_jensenBoundDenominatorChars = some (595666510099486808871532642638469313025154928865966792099946607886787220989739859944102905343608599993436471674120283 : Int) := by decide +kernel

theorem geometryRow141_jensenBound_denominator_nonzero : (595666510099486808871532642638469313025154928865966792099946607886787220989739859944102905343608599993436471674120283 : Int) ≠ 0 := by decide +kernel

theorem geometryRow141_jensenBound_parse :
    parseRational geometryRow141_jensenBoundText = .ok geometryRowsTyped141.jensenBound :=
  original_rational_fraction_of_chars geometryRow141_jensenBoundNumeratorChars geometryRow141_jensenBoundDenominatorChars
    (1955775586924486970297198125649776105831531972200880929665547371470316586440293212890625000000000000 : Int) (595666510099486808871532642638469313025154928865966792099946607886787220989739859944102905343608599993436471674120283 : Int)
    geometryRow141_jensenBound_numerator_no_slash geometryRow141_jensenBound_numerator_parse
    geometryRow141_jensenBound_denominator_parse geometryRow141_jensenBound_denominator_nonzero

theorem geometryRow141_jensenBound_read :
    rationalField geometryRowsJson141 "jensen_bound" = .ok geometryRowsTyped141.jensenBound :=
  original_rationalField_of_string geometryRowsJson141 "jensen_bound" geometryRow141_jensenBoundText
    geometryRowsTyped141.jensenBound geometryRow141_jensenBound_field geometryRow141_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_factorMaxima_before"
  err.flush

theorem geometryRow141_factorMaxima_read :
    rationalArrayField geometryRowsJson141 "factor_maxima" = .ok geometryRowsTyped141.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_gapWeightedMeans_before"
  err.flush

theorem geometryRow141_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson141 "gap_weighted_means" = .ok geometryRowsTyped141.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow141_floorChars : List Char := ['2', '6', '0', '1', '3', '2', '9', '8', '2', '8', '2', '6']
noncomputable def geometryRow141_floorText : String := String.ofList geometryRow141_floorChars

theorem geometryRow141_floor_text_read :
    geometryRowsJson141.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow141_floorText := by rfl

theorem geometryRow141_floor_chars_parse :
    SourceJson.intChars geometryRow141_floorChars = some (260132982826 : Int) := by decide +kernel

theorem geometryRow141_floor_parse :
    parseInteger geometryRow141_floorText = .ok geometryRowsTyped141.jensenFloorQ96 := by
  simp only [geometryRow141_floorText, parseInteger, String.toList_ofList, geometryRow141_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_141 :
    decodeGeometryRow geometryRowsJson141 = .ok geometryRowsTyped141 :=
  original_geometryRow_of_fields geometryRowsJson141 geometryRowsTyped141 geometryRow141_floorText
    geometryRow141_simplexId_read geometryRow141_vertexIds_read
    geometryRow141_physicalVolume_read geometryRow141_meanGap_read
    geometryRow141_factorMaxima_read geometryRow141_gapWeightedMeans_read
    geometryRow141_jensenBound_read geometryRow141_floor_text_read geometryRow141_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_141_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock071 : List SourceJson := [geometryRowsJson140, geometryRowsJson141]
noncomputable def geometryRowsTypedBlock071 : List (GeometryRow) := [geometryRowsTyped140, geometryRowsTyped141]
noncomputable def geometryRowsTypedThroughBlock071 : List (GeometryRow) := geometryRowsTypedThroughBlock070 ++ geometryRowsTypedBlock071

theorem geometry_Rows_block_071_push_eq (acc : List SourceJson) :
    SimplicesBlock071.blockPush acc = [geometryRowsJson141, geometryRowsJson140] ++ acc := by rfl

theorem geometry_Rows_block_071_reverse (acc : List SourceJson) :
    (SimplicesBlock071.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock071 := by
  rw [geometry_Rows_block_071_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_071 :
    geometryRowsJsonBlock071.mapM decodeGeometryRow = .ok geometryRowsTypedBlock071 := by
  simp only [geometryRowsJsonBlock071, geometryRowsTypedBlock071, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_140, decode_geometry_Rows_141]
  rfl

theorem decode_geometry_Rows_through_block_071 :
    SimplicesValue.arrayAcc072.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock071 := by
  change (SimplicesBlock071.blockPush SimplicesValue.arrayAcc071).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_071_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_070, decode_geometry_Rows_block_071]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_071_complete"
  err.flush

#print axioms geometryRow140_simplexId_read
#print axioms geometryRow140_vertexIds_read
#print axioms geometryRow140_physicalVolume_field
#print axioms geometryRow140_physicalVolume_numerator_no_slash
#print axioms geometryRow140_physicalVolume_numerator_parse
#print axioms geometryRow140_physicalVolume_denominator_parse
#print axioms geometryRow140_physicalVolume_denominator_nonzero
#print axioms geometryRow140_physicalVolume_parse
#print axioms geometryRow140_physicalVolume_read
#print axioms geometryRow140_meanGap_field
#print axioms geometryRow140_meanGap_numerator_no_slash
#print axioms geometryRow140_meanGap_numerator_parse
#print axioms geometryRow140_meanGap_denominator_parse
#print axioms geometryRow140_meanGap_denominator_nonzero
#print axioms geometryRow140_meanGap_parse
#print axioms geometryRow140_meanGap_read
#print axioms geometryRow140_jensenBound_field
#print axioms geometryRow140_jensenBound_numerator_no_slash
#print axioms geometryRow140_jensenBound_numerator_parse
#print axioms geometryRow140_jensenBound_denominator_parse
#print axioms geometryRow140_jensenBound_denominator_nonzero
#print axioms geometryRow140_jensenBound_parse
#print axioms geometryRow140_jensenBound_read
#print axioms geometryRow140_factorMaxima_read
#print axioms geometryRow140_gapWeightedMeans_read
#print axioms geometryRow140_floor_text_read
#print axioms geometryRow140_floor_chars_parse
#print axioms geometryRow140_floor_parse
#print axioms decode_geometry_Rows_140
#print axioms geometryRow141_simplexId_read
#print axioms geometryRow141_vertexIds_read
#print axioms geometryRow141_physicalVolume_field
#print axioms geometryRow141_physicalVolume_numerator_no_slash
#print axioms geometryRow141_physicalVolume_numerator_parse
#print axioms geometryRow141_physicalVolume_denominator_parse
#print axioms geometryRow141_physicalVolume_denominator_nonzero
#print axioms geometryRow141_physicalVolume_parse
#print axioms geometryRow141_physicalVolume_read
#print axioms geometryRow141_meanGap_field
#print axioms geometryRow141_meanGap_numerator_no_slash
#print axioms geometryRow141_meanGap_numerator_parse
#print axioms geometryRow141_meanGap_denominator_parse
#print axioms geometryRow141_meanGap_denominator_nonzero
#print axioms geometryRow141_meanGap_parse
#print axioms geometryRow141_meanGap_read
#print axioms geometryRow141_jensenBound_field
#print axioms geometryRow141_jensenBound_numerator_no_slash
#print axioms geometryRow141_jensenBound_numerator_parse
#print axioms geometryRow141_jensenBound_denominator_parse
#print axioms geometryRow141_jensenBound_denominator_nonzero
#print axioms geometryRow141_jensenBound_parse
#print axioms geometryRow141_jensenBound_read
#print axioms geometryRow141_factorMaxima_read
#print axioms geometryRow141_gapWeightedMeans_read
#print axioms geometryRow141_floor_text_read
#print axioms geometryRow141_floor_chars_parse
#print axioms geometryRow141_floor_parse
#print axioms decode_geometry_Rows_141
#print axioms geometry_Rows_block_071_push_eq
#print axioms geometry_Rows_block_071_reverse
#print axioms decode_geometry_Rows_block_071
#print axioms decode_geometry_Rows_through_block_071

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
