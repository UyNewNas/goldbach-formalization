import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows061

/-! Original simplices typed block 62, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson122 : SourceJson :=
  (SimplicesBlock062.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped122 : GeometryRow :=
  { simplexId := 122,
    vertexIds := #[39, 38, 34, 29, 28, 10, 8, 3, 1],
    physicalVolume := ((2722433772359355097783500975748277471 : ℚ) / (1386133585920000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((91731224497 : ℚ) / (1060800000000 : ℚ)), ((92803524817 : ℚ) / (1060800000000 : ℚ)), ((1994432491 : ℚ) / (13600000000 : ℚ)), ((124430278231 : ℚ) / (1060800000000 : ℚ)), ((1345745979 : ℚ) / (20800000000 : ℚ)), ((8128987337 : ℚ) / (176800000000 : ℚ)), ((52714757671 : ℚ) / (1414400000000 : ℚ)), ((149340510383 : ℚ) / (4243200000000 : ℚ)), ((11094083009 : ℚ) / (353600000000 : ℚ)), ((33282178307 : ℚ) / (1060800000000 : ℚ))],
    jensenBound := ((36303155604412307536578411937625886581052282705267066384865034240000000000000000000000000 : ℚ) / (4113057562901653601654418256954312157639348151410369156010714282731430530473618530624811895560675335591 : ℚ)),
    jensenFloorQ96 := (699292987764046 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_simplexId_before"
  err.flush

theorem geometryRow122_simplexId_read :
    geometryRowsJson122.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped122.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_vertexIds_before"
  err.flush

theorem geometryRow122_vertexIds_read :
    geometryRowsJson122.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped122.vertexIds := by decide +kernel

noncomputable def geometryRow122_physicalVolumeNumeratorChars : List Char := ['2', '7', '2', '2', '4', '3', '3', '7', '7', '2', '3', '5', '9', '3', '5', '5', '0', '9', '7', '7', '8', '3', '5', '0', '0', '9', '7', '5', '7', '4', '8', '2', '7', '7', '4', '7', '1']
noncomputable def geometryRow122_physicalVolumeDenominatorChars : List Char := ['1', '3', '8', '6', '1', '3', '3', '5', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow122_physicalVolumeText : String := String.ofList (geometryRow122_physicalVolumeNumeratorChars ++ '/' :: geometryRow122_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_physicalVolume_before_field"
  err.flush

theorem geometryRow122_physicalVolume_field :
    geometryRowsJson122.getObjVal? "physical_volume" = .ok (.str geometryRow122_physicalVolumeText) := by rfl

theorem geometryRow122_physicalVolume_numerator_no_slash :
    geometryRow122_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow122_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow122_physicalVolumeNumeratorChars = some (2722433772359355097783500975748277471 : Int) := by decide +kernel

theorem geometryRow122_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow122_physicalVolumeDenominatorChars = some (1386133585920000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow122_physicalVolume_denominator_nonzero : (1386133585920000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow122_physicalVolume_parse :
    parseRational geometryRow122_physicalVolumeText = .ok geometryRowsTyped122.physicalVolume :=
  original_rational_fraction_of_chars geometryRow122_physicalVolumeNumeratorChars geometryRow122_physicalVolumeDenominatorChars
    (2722433772359355097783500975748277471 : Int) (1386133585920000000000000000000000000000000000000000000000000 : Int)
    geometryRow122_physicalVolume_numerator_no_slash geometryRow122_physicalVolume_numerator_parse
    geometryRow122_physicalVolume_denominator_parse geometryRow122_physicalVolume_denominator_nonzero

theorem geometryRow122_physicalVolume_read :
    rationalField geometryRowsJson122 "physical_volume" = .ok geometryRowsTyped122.physicalVolume :=
  original_rationalField_of_string geometryRowsJson122 "physical_volume" geometryRow122_physicalVolumeText
    geometryRowsTyped122.physicalVolume geometryRow122_physicalVolume_field geometryRow122_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_physicalVolume_complete"
  err.flush

noncomputable def geometryRow122_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow122_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow122_meanGapText : String := String.ofList (geometryRow122_meanGapNumeratorChars ++ '/' :: geometryRow122_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_meanGap_before_field"
  err.flush

theorem geometryRow122_meanGap_field :
    geometryRowsJson122.getObjVal? "mean_gap" = .ok (.str geometryRow122_meanGapText) := by rfl

theorem geometryRow122_meanGap_numerator_no_slash :
    geometryRow122_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow122_meanGap_numerator_parse :
    SourceJson.intChars geometryRow122_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow122_meanGap_denominator_parse :
    SourceJson.intChars geometryRow122_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow122_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow122_meanGap_parse :
    parseRational geometryRow122_meanGapText = .ok geometryRowsTyped122.meanGap :=
  original_rational_fraction_of_chars geometryRow122_meanGapNumeratorChars geometryRow122_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow122_meanGap_numerator_no_slash geometryRow122_meanGap_numerator_parse
    geometryRow122_meanGap_denominator_parse geometryRow122_meanGap_denominator_nonzero

theorem geometryRow122_meanGap_read :
    rationalField geometryRowsJson122 "mean_gap" = .ok geometryRowsTyped122.meanGap :=
  original_rationalField_of_string geometryRowsJson122 "mean_gap" geometryRow122_meanGapText
    geometryRowsTyped122.meanGap geometryRow122_meanGap_field geometryRow122_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_meanGap_complete"
  err.flush

noncomputable def geometryRow122_jensenBoundNumeratorChars : List Char := ['3', '6', '3', '0', '3', '1', '5', '5', '6', '0', '4', '4', '1', '2', '3', '0', '7', '5', '3', '6', '5', '7', '8', '4', '1', '1', '9', '3', '7', '6', '2', '5', '8', '8', '6', '5', '8', '1', '0', '5', '2', '2', '8', '2', '7', '0', '5', '2', '6', '7', '0', '6', '6', '3', '8', '4', '8', '6', '5', '0', '3', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow122_jensenBoundDenominatorChars : List Char := ['4', '1', '1', '3', '0', '5', '7', '5', '6', '2', '9', '0', '1', '6', '5', '3', '6', '0', '1', '6', '5', '4', '4', '1', '8', '2', '5', '6', '9', '5', '4', '3', '1', '2', '1', '5', '7', '6', '3', '9', '3', '4', '8', '1', '5', '1', '4', '1', '0', '3', '6', '9', '1', '5', '6', '0', '1', '0', '7', '1', '4', '2', '8', '2', '7', '3', '1', '4', '3', '0', '5', '3', '0', '4', '7', '3', '6', '1', '8', '5', '3', '0', '6', '2', '4', '8', '1', '1', '8', '9', '5', '5', '6', '0', '6', '7', '5', '3', '3', '5', '5', '9', '1']
noncomputable def geometryRow122_jensenBoundText : String := String.ofList (geometryRow122_jensenBoundNumeratorChars ++ '/' :: geometryRow122_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_jensenBound_before_field"
  err.flush

theorem geometryRow122_jensenBound_field :
    geometryRowsJson122.getObjVal? "jensen_bound" = .ok (.str geometryRow122_jensenBoundText) := by rfl

theorem geometryRow122_jensenBound_numerator_no_slash :
    geometryRow122_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow122_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow122_jensenBoundNumeratorChars = some (36303155604412307536578411937625886581052282705267066384865034240000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow122_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow122_jensenBoundDenominatorChars = some (4113057562901653601654418256954312157639348151410369156010714282731430530473618530624811895560675335591 : Int) := by decide +kernel

theorem geometryRow122_jensenBound_denominator_nonzero : (4113057562901653601654418256954312157639348151410369156010714282731430530473618530624811895560675335591 : Int) ≠ 0 := by decide +kernel

theorem geometryRow122_jensenBound_parse :
    parseRational geometryRow122_jensenBoundText = .ok geometryRowsTyped122.jensenBound :=
  original_rational_fraction_of_chars geometryRow122_jensenBoundNumeratorChars geometryRow122_jensenBoundDenominatorChars
    (36303155604412307536578411937625886581052282705267066384865034240000000000000000000000000 : Int) (4113057562901653601654418256954312157639348151410369156010714282731430530473618530624811895560675335591 : Int)
    geometryRow122_jensenBound_numerator_no_slash geometryRow122_jensenBound_numerator_parse
    geometryRow122_jensenBound_denominator_parse geometryRow122_jensenBound_denominator_nonzero

theorem geometryRow122_jensenBound_read :
    rationalField geometryRowsJson122 "jensen_bound" = .ok geometryRowsTyped122.jensenBound :=
  original_rationalField_of_string geometryRowsJson122 "jensen_bound" geometryRow122_jensenBoundText
    geometryRowsTyped122.jensenBound geometryRow122_jensenBound_field geometryRow122_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_factorMaxima_before"
  err.flush

theorem geometryRow122_factorMaxima_read :
    rationalArrayField geometryRowsJson122 "factor_maxima" = .ok geometryRowsTyped122.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_gapWeightedMeans_before"
  err.flush

theorem geometryRow122_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson122 "gap_weighted_means" = .ok geometryRowsTyped122.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow122_floorChars : List Char := ['6', '9', '9', '2', '9', '2', '9', '8', '7', '7', '6', '4', '0', '4', '6']
noncomputable def geometryRow122_floorText : String := String.ofList geometryRow122_floorChars

theorem geometryRow122_floor_text_read :
    geometryRowsJson122.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow122_floorText := by rfl

theorem geometryRow122_floor_chars_parse :
    SourceJson.intChars geometryRow122_floorChars = some (699292987764046 : Int) := by decide +kernel

theorem geometryRow122_floor_parse :
    parseInteger geometryRow122_floorText = .ok geometryRowsTyped122.jensenFloorQ96 := by
  simp only [geometryRow122_floorText, parseInteger, String.toList_ofList, geometryRow122_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_122 :
    decodeGeometryRow geometryRowsJson122 = .ok geometryRowsTyped122 :=
  original_geometryRow_of_fields geometryRowsJson122 geometryRowsTyped122 geometryRow122_floorText
    geometryRow122_simplexId_read geometryRow122_vertexIds_read
    geometryRow122_physicalVolume_read geometryRow122_meanGap_read
    geometryRow122_factorMaxima_read geometryRow122_gapWeightedMeans_read
    geometryRow122_jensenBound_read geometryRow122_floor_text_read geometryRow122_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_122_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson123 : SourceJson :=
  (SimplicesBlock062.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped123 : GeometryRow :=
  { simplexId := 123,
    vertexIds := #[39, 38, 34, 29, 11, 10, 8, 3, 1],
    physicalVolume := ((5592343303089339666920219832284531 : ℚ) / (2406481920000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((185881752569 : ℚ) / (2121600000000 : ℚ)), ((188026353209 : ℚ) / (2121600000000 : ℚ)), ((11904561521 : ℚ) / (81600000000 : ℚ)), ((246441252887 : ℚ) / (2121600000000 : ℚ)), ((7837289249 : ℚ) / (124800000000 : ℚ)), ((49580358547 : ℚ) / (1060800000000 : ℚ)), ((13814324369 : ℚ) / (353600000000 : ℚ)), ((73275749059 : ℚ) / (2121600000000 : ℚ)), ((67370932579 : ℚ) / (2121600000000 : ℚ)), ((67370791139 : ℚ) / (2121600000000 : ℚ))],
    jensenBound := ((1818499489629513614592869097188860174466268724269857723397790802903040000000000000000000000000 : ℚ) / (183059366134062275845573796045800863096880690277206776212513509225852366427426641884102173691386165244598151 : ℚ)),
    jensenFloorQ96 := (787047263077271 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_simplexId_before"
  err.flush

theorem geometryRow123_simplexId_read :
    geometryRowsJson123.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped123.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_vertexIds_before"
  err.flush

theorem geometryRow123_vertexIds_read :
    geometryRowsJson123.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped123.vertexIds := by decide +kernel

noncomputable def geometryRow123_physicalVolumeNumeratorChars : List Char := ['5', '5', '9', '2', '3', '4', '3', '3', '0', '3', '0', '8', '9', '3', '3', '9', '6', '6', '6', '9', '2', '0', '2', '1', '9', '8', '3', '2', '2', '8', '4', '5', '3', '1']
noncomputable def geometryRow123_physicalVolumeDenominatorChars : List Char := ['2', '4', '0', '6', '4', '8', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow123_physicalVolumeText : String := String.ofList (geometryRow123_physicalVolumeNumeratorChars ++ '/' :: geometryRow123_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_physicalVolume_before_field"
  err.flush

theorem geometryRow123_physicalVolume_field :
    geometryRowsJson123.getObjVal? "physical_volume" = .ok (.str geometryRow123_physicalVolumeText) := by rfl

theorem geometryRow123_physicalVolume_numerator_no_slash :
    geometryRow123_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow123_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow123_physicalVolumeNumeratorChars = some (5592343303089339666920219832284531 : Int) := by decide +kernel

theorem geometryRow123_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow123_physicalVolumeDenominatorChars = some (2406481920000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow123_physicalVolume_denominator_nonzero : (2406481920000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow123_physicalVolume_parse :
    parseRational geometryRow123_physicalVolumeText = .ok geometryRowsTyped123.physicalVolume :=
  original_rational_fraction_of_chars geometryRow123_physicalVolumeNumeratorChars geometryRow123_physicalVolumeDenominatorChars
    (5592343303089339666920219832284531 : Int) (2406481920000000000000000000000000000000000000000000000000 : Int)
    geometryRow123_physicalVolume_numerator_no_slash geometryRow123_physicalVolume_numerator_parse
    geometryRow123_physicalVolume_denominator_parse geometryRow123_physicalVolume_denominator_nonzero

theorem geometryRow123_physicalVolume_read :
    rationalField geometryRowsJson123 "physical_volume" = .ok geometryRowsTyped123.physicalVolume :=
  original_rationalField_of_string geometryRowsJson123 "physical_volume" geometryRow123_physicalVolumeText
    geometryRowsTyped123.physicalVolume geometryRow123_physicalVolume_field geometryRow123_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_physicalVolume_complete"
  err.flush

noncomputable def geometryRow123_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow123_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow123_meanGapText : String := String.ofList (geometryRow123_meanGapNumeratorChars ++ '/' :: geometryRow123_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_meanGap_before_field"
  err.flush

theorem geometryRow123_meanGap_field :
    geometryRowsJson123.getObjVal? "mean_gap" = .ok (.str geometryRow123_meanGapText) := by rfl

theorem geometryRow123_meanGap_numerator_no_slash :
    geometryRow123_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow123_meanGap_numerator_parse :
    SourceJson.intChars geometryRow123_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow123_meanGap_denominator_parse :
    SourceJson.intChars geometryRow123_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow123_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow123_meanGap_parse :
    parseRational geometryRow123_meanGapText = .ok geometryRowsTyped123.meanGap :=
  original_rational_fraction_of_chars geometryRow123_meanGapNumeratorChars geometryRow123_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow123_meanGap_numerator_no_slash geometryRow123_meanGap_numerator_parse
    geometryRow123_meanGap_denominator_parse geometryRow123_meanGap_denominator_nonzero

theorem geometryRow123_meanGap_read :
    rationalField geometryRowsJson123 "mean_gap" = .ok geometryRowsTyped123.meanGap :=
  original_rationalField_of_string geometryRowsJson123 "mean_gap" geometryRow123_meanGapText
    geometryRowsTyped123.meanGap geometryRow123_meanGap_field geometryRow123_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_meanGap_complete"
  err.flush

noncomputable def geometryRow123_jensenBoundNumeratorChars : List Char := ['1', '8', '1', '8', '4', '9', '9', '4', '8', '9', '6', '2', '9', '5', '1', '3', '6', '1', '4', '5', '9', '2', '8', '6', '9', '0', '9', '7', '1', '8', '8', '8', '6', '0', '1', '7', '4', '4', '6', '6', '2', '6', '8', '7', '2', '4', '2', '6', '9', '8', '5', '7', '7', '2', '3', '3', '9', '7', '7', '9', '0', '8', '0', '2', '9', '0', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow123_jensenBoundDenominatorChars : List Char := ['1', '8', '3', '0', '5', '9', '3', '6', '6', '1', '3', '4', '0', '6', '2', '2', '7', '5', '8', '4', '5', '5', '7', '3', '7', '9', '6', '0', '4', '5', '8', '0', '0', '8', '6', '3', '0', '9', '6', '8', '8', '0', '6', '9', '0', '2', '7', '7', '2', '0', '6', '7', '7', '6', '2', '1', '2', '5', '1', '3', '5', '0', '9', '2', '2', '5', '8', '5', '2', '3', '6', '6', '4', '2', '7', '4', '2', '6', '6', '4', '1', '8', '8', '4', '1', '0', '2', '1', '7', '3', '6', '9', '1', '3', '8', '6', '1', '6', '5', '2', '4', '4', '5', '9', '8', '1', '5', '1']
noncomputable def geometryRow123_jensenBoundText : String := String.ofList (geometryRow123_jensenBoundNumeratorChars ++ '/' :: geometryRow123_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_jensenBound_before_field"
  err.flush

theorem geometryRow123_jensenBound_field :
    geometryRowsJson123.getObjVal? "jensen_bound" = .ok (.str geometryRow123_jensenBoundText) := by rfl

theorem geometryRow123_jensenBound_numerator_no_slash :
    geometryRow123_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow123_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow123_jensenBoundNumeratorChars = some (1818499489629513614592869097188860174466268724269857723397790802903040000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow123_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow123_jensenBoundDenominatorChars = some (183059366134062275845573796045800863096880690277206776212513509225852366427426641884102173691386165244598151 : Int) := by decide +kernel

theorem geometryRow123_jensenBound_denominator_nonzero : (183059366134062275845573796045800863096880690277206776212513509225852366427426641884102173691386165244598151 : Int) ≠ 0 := by decide +kernel

theorem geometryRow123_jensenBound_parse :
    parseRational geometryRow123_jensenBoundText = .ok geometryRowsTyped123.jensenBound :=
  original_rational_fraction_of_chars geometryRow123_jensenBoundNumeratorChars geometryRow123_jensenBoundDenominatorChars
    (1818499489629513614592869097188860174466268724269857723397790802903040000000000000000000000000 : Int) (183059366134062275845573796045800863096880690277206776212513509225852366427426641884102173691386165244598151 : Int)
    geometryRow123_jensenBound_numerator_no_slash geometryRow123_jensenBound_numerator_parse
    geometryRow123_jensenBound_denominator_parse geometryRow123_jensenBound_denominator_nonzero

theorem geometryRow123_jensenBound_read :
    rationalField geometryRowsJson123 "jensen_bound" = .ok geometryRowsTyped123.jensenBound :=
  original_rationalField_of_string geometryRowsJson123 "jensen_bound" geometryRow123_jensenBoundText
    geometryRowsTyped123.jensenBound geometryRow123_jensenBound_field geometryRow123_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_factorMaxima_before"
  err.flush

theorem geometryRow123_factorMaxima_read :
    rationalArrayField geometryRowsJson123 "factor_maxima" = .ok geometryRowsTyped123.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_gapWeightedMeans_before"
  err.flush

theorem geometryRow123_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson123 "gap_weighted_means" = .ok geometryRowsTyped123.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow123_floorChars : List Char := ['7', '8', '7', '0', '4', '7', '2', '6', '3', '0', '7', '7', '2', '7', '1']
noncomputable def geometryRow123_floorText : String := String.ofList geometryRow123_floorChars

theorem geometryRow123_floor_text_read :
    geometryRowsJson123.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow123_floorText := by rfl

theorem geometryRow123_floor_chars_parse :
    SourceJson.intChars geometryRow123_floorChars = some (787047263077271 : Int) := by decide +kernel

theorem geometryRow123_floor_parse :
    parseInteger geometryRow123_floorText = .ok geometryRowsTyped123.jensenFloorQ96 := by
  simp only [geometryRow123_floorText, parseInteger, String.toList_ofList, geometryRow123_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_123 :
    decodeGeometryRow geometryRowsJson123 = .ok geometryRowsTyped123 :=
  original_geometryRow_of_fields geometryRowsJson123 geometryRowsTyped123 geometryRow123_floorText
    geometryRow123_simplexId_read geometryRow123_vertexIds_read
    geometryRow123_physicalVolume_read geometryRow123_meanGap_read
    geometryRow123_factorMaxima_read geometryRow123_gapWeightedMeans_read
    geometryRow123_jensenBound_read geometryRow123_floor_text_read geometryRow123_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_123_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock062 : List SourceJson := [geometryRowsJson122, geometryRowsJson123]
noncomputable def geometryRowsTypedBlock062 : List (GeometryRow) := [geometryRowsTyped122, geometryRowsTyped123]
noncomputable def geometryRowsTypedThroughBlock062 : List (GeometryRow) := geometryRowsTypedThroughBlock061 ++ geometryRowsTypedBlock062

theorem geometry_Rows_block_062_push_eq (acc : List SourceJson) :
    SimplicesBlock062.blockPush acc = [geometryRowsJson123, geometryRowsJson122] ++ acc := by rfl

theorem geometry_Rows_block_062_reverse (acc : List SourceJson) :
    (SimplicesBlock062.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock062 := by
  rw [geometry_Rows_block_062_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_062 :
    geometryRowsJsonBlock062.mapM decodeGeometryRow = .ok geometryRowsTypedBlock062 := by
  simp only [geometryRowsJsonBlock062, geometryRowsTypedBlock062, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_122, decode_geometry_Rows_123]
  rfl

theorem decode_geometry_Rows_through_block_062 :
    SimplicesValue.arrayAcc063.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock062 := by
  change (SimplicesBlock062.blockPush SimplicesValue.arrayAcc062).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_062_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_061, decode_geometry_Rows_block_062]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_062_complete"
  err.flush

#print axioms geometryRow122_simplexId_read
#print axioms geometryRow122_vertexIds_read
#print axioms geometryRow122_physicalVolume_field
#print axioms geometryRow122_physicalVolume_numerator_no_slash
#print axioms geometryRow122_physicalVolume_numerator_parse
#print axioms geometryRow122_physicalVolume_denominator_parse
#print axioms geometryRow122_physicalVolume_denominator_nonzero
#print axioms geometryRow122_physicalVolume_parse
#print axioms geometryRow122_physicalVolume_read
#print axioms geometryRow122_meanGap_field
#print axioms geometryRow122_meanGap_numerator_no_slash
#print axioms geometryRow122_meanGap_numerator_parse
#print axioms geometryRow122_meanGap_denominator_parse
#print axioms geometryRow122_meanGap_denominator_nonzero
#print axioms geometryRow122_meanGap_parse
#print axioms geometryRow122_meanGap_read
#print axioms geometryRow122_jensenBound_field
#print axioms geometryRow122_jensenBound_numerator_no_slash
#print axioms geometryRow122_jensenBound_numerator_parse
#print axioms geometryRow122_jensenBound_denominator_parse
#print axioms geometryRow122_jensenBound_denominator_nonzero
#print axioms geometryRow122_jensenBound_parse
#print axioms geometryRow122_jensenBound_read
#print axioms geometryRow122_factorMaxima_read
#print axioms geometryRow122_gapWeightedMeans_read
#print axioms geometryRow122_floor_text_read
#print axioms geometryRow122_floor_chars_parse
#print axioms geometryRow122_floor_parse
#print axioms decode_geometry_Rows_122
#print axioms geometryRow123_simplexId_read
#print axioms geometryRow123_vertexIds_read
#print axioms geometryRow123_physicalVolume_field
#print axioms geometryRow123_physicalVolume_numerator_no_slash
#print axioms geometryRow123_physicalVolume_numerator_parse
#print axioms geometryRow123_physicalVolume_denominator_parse
#print axioms geometryRow123_physicalVolume_denominator_nonzero
#print axioms geometryRow123_physicalVolume_parse
#print axioms geometryRow123_physicalVolume_read
#print axioms geometryRow123_meanGap_field
#print axioms geometryRow123_meanGap_numerator_no_slash
#print axioms geometryRow123_meanGap_numerator_parse
#print axioms geometryRow123_meanGap_denominator_parse
#print axioms geometryRow123_meanGap_denominator_nonzero
#print axioms geometryRow123_meanGap_parse
#print axioms geometryRow123_meanGap_read
#print axioms geometryRow123_jensenBound_field
#print axioms geometryRow123_jensenBound_numerator_no_slash
#print axioms geometryRow123_jensenBound_numerator_parse
#print axioms geometryRow123_jensenBound_denominator_parse
#print axioms geometryRow123_jensenBound_denominator_nonzero
#print axioms geometryRow123_jensenBound_parse
#print axioms geometryRow123_jensenBound_read
#print axioms geometryRow123_factorMaxima_read
#print axioms geometryRow123_gapWeightedMeans_read
#print axioms geometryRow123_floor_text_read
#print axioms geometryRow123_floor_chars_parse
#print axioms geometryRow123_floor_parse
#print axioms decode_geometry_Rows_123
#print axioms geometry_Rows_block_062_push_eq
#print axioms geometry_Rows_block_062_reverse
#print axioms decode_geometry_Rows_block_062
#print axioms decode_geometry_Rows_through_block_062

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
