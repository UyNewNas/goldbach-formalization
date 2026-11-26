import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows012

/-! Original simplices typed block 13, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson026 : SourceJson :=
  (SimplicesBlock013.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped026 : GeometryRow :=
  { simplexId := 26,
    vertexIds := #[39, 35, 29, 27, 26, 17, 12, 4, 2],
    physicalVolume := ((7480526953816946931858874670609290889281 : ℚ) / (15663692880281600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((591629 : ℚ) / (517440000 : ℚ)),
    factorMaxima := #[((1021879 : ℚ) / (11200000 : ℚ)), ((37827897 : ℚ) / (392000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2784283 : ℚ) / (33600000 : ℚ)), ((8952977 : ℚ) / (168000000 : ℚ)), ((4546639 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((308977381958770561 : ℚ) / (3807805848000000000 : ℚ)), ((146932771728235489 : ℚ) / (1776976062400000000 : ℚ)), ((648186698563205749 : ℚ) / (4442440156000000000 : ℚ)), ((635563825535262301 : ℚ) / (5330928187200000000 : ℚ)), ((126508389256356301 : ℚ) / (1776976062400000000 : ℚ)), ((121698937586536589 : ℚ) / (2665464093600000000 : ℚ)), ((493923204746867551 : ℚ) / (13327320468000000000 : ℚ)), ((877240117108952677 : ℚ) / (26654640936000000000 : ℚ)), ((292412780044296759 : ℚ) / (8884880312000000000 : ℚ)), ((158730835481814361 : ℚ) / (5330928187200000000 : ℚ))],
    jensenBound := ((3099204742815258535434233756387743639063762795199737518207144334208311167945610467573403139983179642958695596977564813954335208320000000000000000000000000000000 : ℚ) / (643433717168663603654803021258962615441940621352739780509280152357474360226594316458173606420047265075510705646665918858576447275358487780494204457100860549758689791104201893 : ℚ)),
    jensenFloorQ96 := (381615526940720 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_simplexId_before"
  err.flush

theorem geometryRow026_simplexId_read :
    geometryRowsJson026.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped026.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_vertexIds_before"
  err.flush

theorem geometryRow026_vertexIds_read :
    geometryRowsJson026.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped026.vertexIds := by decide +kernel

noncomputable def geometryRow026_physicalVolumeNumeratorChars : List Char := ['7', '4', '8', '0', '5', '2', '6', '9', '5', '3', '8', '1', '6', '9', '4', '6', '9', '3', '1', '8', '5', '8', '8', '7', '4', '6', '7', '0', '6', '0', '9', '2', '9', '0', '8', '8', '9', '2', '8', '1']
noncomputable def geometryRow026_physicalVolumeDenominatorChars : List Char := ['1', '5', '6', '6', '3', '6', '9', '2', '8', '8', '0', '2', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow026_physicalVolumeText : String := String.ofList (geometryRow026_physicalVolumeNumeratorChars ++ '/' :: geometryRow026_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_physicalVolume_before_field"
  err.flush

theorem geometryRow026_physicalVolume_field :
    geometryRowsJson026.getObjVal? "physical_volume" = .ok (.str geometryRow026_physicalVolumeText) := by rfl

theorem geometryRow026_physicalVolume_numerator_no_slash :
    geometryRow026_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow026_physicalVolumeNumeratorChars = some (7480526953816946931858874670609290889281 : Int) := by decide +kernel

theorem geometryRow026_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow026_physicalVolumeDenominatorChars = some (15663692880281600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow026_physicalVolume_denominator_nonzero : (15663692880281600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_physicalVolume_parse :
    parseRational geometryRow026_physicalVolumeText = .ok geometryRowsTyped026.physicalVolume :=
  original_rational_fraction_of_chars geometryRow026_physicalVolumeNumeratorChars geometryRow026_physicalVolumeDenominatorChars
    (7480526953816946931858874670609290889281 : Int) (15663692880281600000000000000000000000000000000000000000000000000 : Int)
    geometryRow026_physicalVolume_numerator_no_slash geometryRow026_physicalVolume_numerator_parse
    geometryRow026_physicalVolume_denominator_parse geometryRow026_physicalVolume_denominator_nonzero

theorem geometryRow026_physicalVolume_read :
    rationalField geometryRowsJson026 "physical_volume" = .ok geometryRowsTyped026.physicalVolume :=
  original_rationalField_of_string geometryRowsJson026 "physical_volume" geometryRow026_physicalVolumeText
    geometryRowsTyped026.physicalVolume geometryRow026_physicalVolume_field geometryRow026_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_physicalVolume_complete"
  err.flush

noncomputable def geometryRow026_meanGapNumeratorChars : List Char := ['5', '9', '1', '6', '2', '9']
noncomputable def geometryRow026_meanGapDenominatorChars : List Char := ['5', '1', '7', '4', '4', '0', '0', '0', '0']
noncomputable def geometryRow026_meanGapText : String := String.ofList (geometryRow026_meanGapNumeratorChars ++ '/' :: geometryRow026_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_meanGap_before_field"
  err.flush

theorem geometryRow026_meanGap_field :
    geometryRowsJson026.getObjVal? "mean_gap" = .ok (.str geometryRow026_meanGapText) := by rfl

theorem geometryRow026_meanGap_numerator_no_slash :
    geometryRow026_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_meanGap_numerator_parse :
    SourceJson.intChars geometryRow026_meanGapNumeratorChars = some (591629 : Int) := by decide +kernel

theorem geometryRow026_meanGap_denominator_parse :
    SourceJson.intChars geometryRow026_meanGapDenominatorChars = some (517440000 : Int) := by decide +kernel

theorem geometryRow026_meanGap_denominator_nonzero : (517440000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_meanGap_parse :
    parseRational geometryRow026_meanGapText = .ok geometryRowsTyped026.meanGap :=
  original_rational_fraction_of_chars geometryRow026_meanGapNumeratorChars geometryRow026_meanGapDenominatorChars
    (591629 : Int) (517440000 : Int)
    geometryRow026_meanGap_numerator_no_slash geometryRow026_meanGap_numerator_parse
    geometryRow026_meanGap_denominator_parse geometryRow026_meanGap_denominator_nonzero

theorem geometryRow026_meanGap_read :
    rationalField geometryRowsJson026 "mean_gap" = .ok geometryRowsTyped026.meanGap :=
  original_rationalField_of_string geometryRowsJson026 "mean_gap" geometryRow026_meanGapText
    geometryRowsTyped026.meanGap geometryRow026_meanGap_field geometryRow026_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_meanGap_complete"
  err.flush

noncomputable def geometryRow026_jensenBoundNumeratorChars : List Char := ['3', '0', '9', '9', '2', '0', '4', '7', '4', '2', '8', '1', '5', '2', '5', '8', '5', '3', '5', '4', '3', '4', '2', '3', '3', '7', '5', '6', '3', '8', '7', '7', '4', '3', '6', '3', '9', '0', '6', '3', '7', '6', '2', '7', '9', '5', '1', '9', '9', '7', '3', '7', '5', '1', '8', '2', '0', '7', '1', '4', '4', '3', '3', '4', '2', '0', '8', '3', '1', '1', '1', '6', '7', '9', '4', '5', '6', '1', '0', '4', '6', '7', '5', '7', '3', '4', '0', '3', '1', '3', '9', '9', '8', '3', '1', '7', '9', '6', '4', '2', '9', '5', '8', '6', '9', '5', '5', '9', '6', '9', '7', '7', '5', '6', '4', '8', '1', '3', '9', '5', '4', '3', '3', '5', '2', '0', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow026_jensenBoundDenominatorChars : List Char := ['6', '4', '3', '4', '3', '3', '7', '1', '7', '1', '6', '8', '6', '6', '3', '6', '0', '3', '6', '5', '4', '8', '0', '3', '0', '2', '1', '2', '5', '8', '9', '6', '2', '6', '1', '5', '4', '4', '1', '9', '4', '0', '6', '2', '1', '3', '5', '2', '7', '3', '9', '7', '8', '0', '5', '0', '9', '2', '8', '0', '1', '5', '2', '3', '5', '7', '4', '7', '4', '3', '6', '0', '2', '2', '6', '5', '9', '4', '3', '1', '6', '4', '5', '8', '1', '7', '3', '6', '0', '6', '4', '2', '0', '0', '4', '7', '2', '6', '5', '0', '7', '5', '5', '1', '0', '7', '0', '5', '6', '4', '6', '6', '6', '5', '9', '1', '8', '8', '5', '8', '5', '7', '6', '4', '4', '7', '2', '7', '5', '3', '5', '8', '4', '8', '7', '7', '8', '0', '4', '9', '4', '2', '0', '4', '4', '5', '7', '1', '0', '0', '8', '6', '0', '5', '4', '9', '7', '5', '8', '6', '8', '9', '7', '9', '1', '1', '0', '4', '2', '0', '1', '8', '9', '3']
noncomputable def geometryRow026_jensenBoundText : String := String.ofList (geometryRow026_jensenBoundNumeratorChars ++ '/' :: geometryRow026_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_jensenBound_before_field"
  err.flush

theorem geometryRow026_jensenBound_field :
    geometryRowsJson026.getObjVal? "jensen_bound" = .ok (.str geometryRow026_jensenBoundText) := by rfl

theorem geometryRow026_jensenBound_numerator_no_slash :
    geometryRow026_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow026_jensenBoundNumeratorChars = some (3099204742815258535434233756387743639063762795199737518207144334208311167945610467573403139983179642958695596977564813954335208320000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow026_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow026_jensenBoundDenominatorChars = some (643433717168663603654803021258962615441940621352739780509280152357474360226594316458173606420047265075510705646665918858576447275358487780494204457100860549758689791104201893 : Int) := by decide +kernel

theorem geometryRow026_jensenBound_denominator_nonzero : (643433717168663603654803021258962615441940621352739780509280152357474360226594316458173606420047265075510705646665918858576447275358487780494204457100860549758689791104201893 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_jensenBound_parse :
    parseRational geometryRow026_jensenBoundText = .ok geometryRowsTyped026.jensenBound :=
  original_rational_fraction_of_chars geometryRow026_jensenBoundNumeratorChars geometryRow026_jensenBoundDenominatorChars
    (3099204742815258535434233756387743639063762795199737518207144334208311167945610467573403139983179642958695596977564813954335208320000000000000000000000000000000 : Int) (643433717168663603654803021258962615441940621352739780509280152357474360226594316458173606420047265075510705646665918858576447275358487780494204457100860549758689791104201893 : Int)
    geometryRow026_jensenBound_numerator_no_slash geometryRow026_jensenBound_numerator_parse
    geometryRow026_jensenBound_denominator_parse geometryRow026_jensenBound_denominator_nonzero

theorem geometryRow026_jensenBound_read :
    rationalField geometryRowsJson026 "jensen_bound" = .ok geometryRowsTyped026.jensenBound :=
  original_rationalField_of_string geometryRowsJson026 "jensen_bound" geometryRow026_jensenBoundText
    geometryRowsTyped026.jensenBound geometryRow026_jensenBound_field geometryRow026_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_factorMaxima_before"
  err.flush

theorem geometryRow026_factorMaxima_read :
    rationalArrayField geometryRowsJson026 "factor_maxima" = .ok geometryRowsTyped026.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_gapWeightedMeans_before"
  err.flush

theorem geometryRow026_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson026 "gap_weighted_means" = .ok geometryRowsTyped026.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow026_floorChars : List Char := ['3', '8', '1', '6', '1', '5', '5', '2', '6', '9', '4', '0', '7', '2', '0']
noncomputable def geometryRow026_floorText : String := String.ofList geometryRow026_floorChars

theorem geometryRow026_floor_text_read :
    geometryRowsJson026.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow026_floorText := by rfl

theorem geometryRow026_floor_chars_parse :
    SourceJson.intChars geometryRow026_floorChars = some (381615526940720 : Int) := by decide +kernel

theorem geometryRow026_floor_parse :
    parseInteger geometryRow026_floorText = .ok geometryRowsTyped026.jensenFloorQ96 := by
  simp only [geometryRow026_floorText, parseInteger, String.toList_ofList, geometryRow026_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_026 :
    decodeGeometryRow geometryRowsJson026 = .ok geometryRowsTyped026 :=
  original_geometryRow_of_fields geometryRowsJson026 geometryRowsTyped026 geometryRow026_floorText
    geometryRow026_simplexId_read geometryRow026_vertexIds_read
    geometryRow026_physicalVolume_read geometryRow026_meanGap_read
    geometryRow026_factorMaxima_read geometryRow026_gapWeightedMeans_read
    geometryRow026_jensenBound_read geometryRow026_floor_text_read geometryRow026_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_026_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson027 : SourceJson :=
  (SimplicesBlock013.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped027 : GeometryRow :=
  { simplexId := 27,
    vertexIds := #[39, 35, 29, 27, 26, 17, 6, 2, 0],
    physicalVolume := ((28528518392418439542903823244083377531451 : ℚ) / (18022146637824000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546639 : ℚ) / (96000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((281391986983 : ℚ) / (3393600000000 : ℚ)), ((1994736948721 : ℚ) / (23755200000000 : ℚ)), ((22948969741 : ℚ) / (158368000000 : ℚ)), ((8324679811313 : ℚ) / (71265600000000 : ℚ)), ((1616075014529 : ℚ) / (23755200000000 : ℚ)), ((185699573387 : ℚ) / (3959200000000 : ℚ)), ((453046943429 : ℚ) / (11877600000000 : ℚ)), ((269173045241 : ℚ) / (7918400000000 : ℚ)), ((807517552043 : ℚ) / (23755200000000 : ℚ)), ((2152457342377 : ℚ) / (71265600000000 : ℚ))],
    jensenBound := ((50426426934128475045344666683925910141279478451436990525606620114352366564176560128000000000000000000000 : ℚ) / (6821216104295881257852807188686930540517922251722635014315806120870301512659268267361889819475136962456552089087404623 : ℚ)),
    jensenFloorQ96 := (585701008011563 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_simplexId_before"
  err.flush

theorem geometryRow027_simplexId_read :
    geometryRowsJson027.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped027.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_vertexIds_before"
  err.flush

theorem geometryRow027_vertexIds_read :
    geometryRowsJson027.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped027.vertexIds := by decide +kernel

noncomputable def geometryRow027_physicalVolumeNumeratorChars : List Char := ['2', '8', '5', '2', '8', '5', '1', '8', '3', '9', '2', '4', '1', '8', '4', '3', '9', '5', '4', '2', '9', '0', '3', '8', '2', '3', '2', '4', '4', '0', '8', '3', '3', '7', '7', '5', '3', '1', '4', '5', '1']
noncomputable def geometryRow027_physicalVolumeDenominatorChars : List Char := ['1', '8', '0', '2', '2', '1', '4', '6', '6', '3', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_physicalVolumeText : String := String.ofList (geometryRow027_physicalVolumeNumeratorChars ++ '/' :: geometryRow027_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_physicalVolume_before_field"
  err.flush

theorem geometryRow027_physicalVolume_field :
    geometryRowsJson027.getObjVal? "physical_volume" = .ok (.str geometryRow027_physicalVolumeText) := by rfl

theorem geometryRow027_physicalVolume_numerator_no_slash :
    geometryRow027_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow027_physicalVolumeNumeratorChars = some (28528518392418439542903823244083377531451 : Int) := by decide +kernel

theorem geometryRow027_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow027_physicalVolumeDenominatorChars = some (18022146637824000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow027_physicalVolume_denominator_nonzero : (18022146637824000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_physicalVolume_parse :
    parseRational geometryRow027_physicalVolumeText = .ok geometryRowsTyped027.physicalVolume :=
  original_rational_fraction_of_chars geometryRow027_physicalVolumeNumeratorChars geometryRow027_physicalVolumeDenominatorChars
    (28528518392418439542903823244083377531451 : Int) (18022146637824000000000000000000000000000000000000000000000000000 : Int)
    geometryRow027_physicalVolume_numerator_no_slash geometryRow027_physicalVolume_numerator_parse
    geometryRow027_physicalVolume_denominator_parse geometryRow027_physicalVolume_denominator_nonzero

theorem geometryRow027_physicalVolume_read :
    rationalField geometryRowsJson027 "physical_volume" = .ok geometryRowsTyped027.physicalVolume :=
  original_rationalField_of_string geometryRowsJson027 "physical_volume" geometryRow027_physicalVolumeText
    geometryRowsTyped027.physicalVolume geometryRow027_physicalVolume_field geometryRow027_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_physicalVolume_complete"
  err.flush

noncomputable def geometryRow027_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow027_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_meanGapText : String := String.ofList (geometryRow027_meanGapNumeratorChars ++ '/' :: geometryRow027_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_meanGap_before_field"
  err.flush

theorem geometryRow027_meanGap_field :
    geometryRowsJson027.getObjVal? "mean_gap" = .ok (.str geometryRow027_meanGapText) := by rfl

theorem geometryRow027_meanGap_numerator_no_slash :
    geometryRow027_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_meanGap_numerator_parse :
    SourceJson.intChars geometryRow027_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow027_meanGap_denominator_parse :
    SourceJson.intChars geometryRow027_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow027_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_meanGap_parse :
    parseRational geometryRow027_meanGapText = .ok geometryRowsTyped027.meanGap :=
  original_rational_fraction_of_chars geometryRow027_meanGapNumeratorChars geometryRow027_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow027_meanGap_numerator_no_slash geometryRow027_meanGap_numerator_parse
    geometryRow027_meanGap_denominator_parse geometryRow027_meanGap_denominator_nonzero

theorem geometryRow027_meanGap_read :
    rationalField geometryRowsJson027 "mean_gap" = .ok geometryRowsTyped027.meanGap :=
  original_rationalField_of_string geometryRowsJson027 "mean_gap" geometryRow027_meanGapText
    geometryRowsTyped027.meanGap geometryRow027_meanGap_field geometryRow027_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_meanGap_complete"
  err.flush

noncomputable def geometryRow027_jensenBoundNumeratorChars : List Char := ['5', '0', '4', '2', '6', '4', '2', '6', '9', '3', '4', '1', '2', '8', '4', '7', '5', '0', '4', '5', '3', '4', '4', '6', '6', '6', '6', '8', '3', '9', '2', '5', '9', '1', '0', '1', '4', '1', '2', '7', '9', '4', '7', '8', '4', '5', '1', '4', '3', '6', '9', '9', '0', '5', '2', '5', '6', '0', '6', '6', '2', '0', '1', '1', '4', '3', '5', '2', '3', '6', '6', '5', '6', '4', '1', '7', '6', '5', '6', '0', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_jensenBoundDenominatorChars : List Char := ['6', '8', '2', '1', '2', '1', '6', '1', '0', '4', '2', '9', '5', '8', '8', '1', '2', '5', '7', '8', '5', '2', '8', '0', '7', '1', '8', '8', '6', '8', '6', '9', '3', '0', '5', '4', '0', '5', '1', '7', '9', '2', '2', '2', '5', '1', '7', '2', '2', '6', '3', '5', '0', '1', '4', '3', '1', '5', '8', '0', '6', '1', '2', '0', '8', '7', '0', '3', '0', '1', '5', '1', '2', '6', '5', '9', '2', '6', '8', '2', '6', '7', '3', '6', '1', '8', '8', '9', '8', '1', '9', '4', '7', '5', '1', '3', '6', '9', '6', '2', '4', '5', '6', '5', '5', '2', '0', '8', '9', '0', '8', '7', '4', '0', '4', '6', '2', '3']
noncomputable def geometryRow027_jensenBoundText : String := String.ofList (geometryRow027_jensenBoundNumeratorChars ++ '/' :: geometryRow027_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_jensenBound_before_field"
  err.flush

theorem geometryRow027_jensenBound_field :
    geometryRowsJson027.getObjVal? "jensen_bound" = .ok (.str geometryRow027_jensenBoundText) := by rfl

theorem geometryRow027_jensenBound_numerator_no_slash :
    geometryRow027_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow027_jensenBoundNumeratorChars = some (50426426934128475045344666683925910141279478451436990525606620114352366564176560128000000000000000000000 : Int) := by decide +kernel

theorem geometryRow027_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow027_jensenBoundDenominatorChars = some (6821216104295881257852807188686930540517922251722635014315806120870301512659268267361889819475136962456552089087404623 : Int) := by decide +kernel

theorem geometryRow027_jensenBound_denominator_nonzero : (6821216104295881257852807188686930540517922251722635014315806120870301512659268267361889819475136962456552089087404623 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_jensenBound_parse :
    parseRational geometryRow027_jensenBoundText = .ok geometryRowsTyped027.jensenBound :=
  original_rational_fraction_of_chars geometryRow027_jensenBoundNumeratorChars geometryRow027_jensenBoundDenominatorChars
    (50426426934128475045344666683925910141279478451436990525606620114352366564176560128000000000000000000000 : Int) (6821216104295881257852807188686930540517922251722635014315806120870301512659268267361889819475136962456552089087404623 : Int)
    geometryRow027_jensenBound_numerator_no_slash geometryRow027_jensenBound_numerator_parse
    geometryRow027_jensenBound_denominator_parse geometryRow027_jensenBound_denominator_nonzero

theorem geometryRow027_jensenBound_read :
    rationalField geometryRowsJson027 "jensen_bound" = .ok geometryRowsTyped027.jensenBound :=
  original_rationalField_of_string geometryRowsJson027 "jensen_bound" geometryRow027_jensenBoundText
    geometryRowsTyped027.jensenBound geometryRow027_jensenBound_field geometryRow027_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_factorMaxima_before"
  err.flush

theorem geometryRow027_factorMaxima_read :
    rationalArrayField geometryRowsJson027 "factor_maxima" = .ok geometryRowsTyped027.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_gapWeightedMeans_before"
  err.flush

theorem geometryRow027_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson027 "gap_weighted_means" = .ok geometryRowsTyped027.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow027_floorChars : List Char := ['5', '8', '5', '7', '0', '1', '0', '0', '8', '0', '1', '1', '5', '6', '3']
noncomputable def geometryRow027_floorText : String := String.ofList geometryRow027_floorChars

theorem geometryRow027_floor_text_read :
    geometryRowsJson027.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow027_floorText := by rfl

theorem geometryRow027_floor_chars_parse :
    SourceJson.intChars geometryRow027_floorChars = some (585701008011563 : Int) := by decide +kernel

theorem geometryRow027_floor_parse :
    parseInteger geometryRow027_floorText = .ok geometryRowsTyped027.jensenFloorQ96 := by
  simp only [geometryRow027_floorText, parseInteger, String.toList_ofList, geometryRow027_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_027 :
    decodeGeometryRow geometryRowsJson027 = .ok geometryRowsTyped027 :=
  original_geometryRow_of_fields geometryRowsJson027 geometryRowsTyped027 geometryRow027_floorText
    geometryRow027_simplexId_read geometryRow027_vertexIds_read
    geometryRow027_physicalVolume_read geometryRow027_meanGap_read
    geometryRow027_factorMaxima_read geometryRow027_gapWeightedMeans_read
    geometryRow027_jensenBound_read geometryRow027_floor_text_read geometryRow027_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_027_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock013 : List SourceJson := [geometryRowsJson026, geometryRowsJson027]
noncomputable def geometryRowsTypedBlock013 : List (GeometryRow) := [geometryRowsTyped026, geometryRowsTyped027]
noncomputable def geometryRowsTypedThroughBlock013 : List (GeometryRow) := geometryRowsTypedThroughBlock012 ++ geometryRowsTypedBlock013

theorem geometry_Rows_block_013_push_eq (acc : List SourceJson) :
    SimplicesBlock013.blockPush acc = [geometryRowsJson027, geometryRowsJson026] ++ acc := by rfl

theorem geometry_Rows_block_013_reverse (acc : List SourceJson) :
    (SimplicesBlock013.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock013 := by
  rw [geometry_Rows_block_013_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_013 :
    geometryRowsJsonBlock013.mapM decodeGeometryRow = .ok geometryRowsTypedBlock013 := by
  simp only [geometryRowsJsonBlock013, geometryRowsTypedBlock013, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_026, decode_geometry_Rows_027]
  rfl

theorem decode_geometry_Rows_through_block_013 :
    SimplicesValue.arrayAcc014.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock013 := by
  change (SimplicesBlock013.blockPush SimplicesValue.arrayAcc013).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_013_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_012, decode_geometry_Rows_block_013]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_013_complete"
  err.flush

#print axioms geometryRow026_simplexId_read
#print axioms geometryRow026_vertexIds_read
#print axioms geometryRow026_physicalVolume_field
#print axioms geometryRow026_physicalVolume_numerator_no_slash
#print axioms geometryRow026_physicalVolume_numerator_parse
#print axioms geometryRow026_physicalVolume_denominator_parse
#print axioms geometryRow026_physicalVolume_denominator_nonzero
#print axioms geometryRow026_physicalVolume_parse
#print axioms geometryRow026_physicalVolume_read
#print axioms geometryRow026_meanGap_field
#print axioms geometryRow026_meanGap_numerator_no_slash
#print axioms geometryRow026_meanGap_numerator_parse
#print axioms geometryRow026_meanGap_denominator_parse
#print axioms geometryRow026_meanGap_denominator_nonzero
#print axioms geometryRow026_meanGap_parse
#print axioms geometryRow026_meanGap_read
#print axioms geometryRow026_jensenBound_field
#print axioms geometryRow026_jensenBound_numerator_no_slash
#print axioms geometryRow026_jensenBound_numerator_parse
#print axioms geometryRow026_jensenBound_denominator_parse
#print axioms geometryRow026_jensenBound_denominator_nonzero
#print axioms geometryRow026_jensenBound_parse
#print axioms geometryRow026_jensenBound_read
#print axioms geometryRow026_factorMaxima_read
#print axioms geometryRow026_gapWeightedMeans_read
#print axioms geometryRow026_floor_text_read
#print axioms geometryRow026_floor_chars_parse
#print axioms geometryRow026_floor_parse
#print axioms decode_geometry_Rows_026
#print axioms geometryRow027_simplexId_read
#print axioms geometryRow027_vertexIds_read
#print axioms geometryRow027_physicalVolume_field
#print axioms geometryRow027_physicalVolume_numerator_no_slash
#print axioms geometryRow027_physicalVolume_numerator_parse
#print axioms geometryRow027_physicalVolume_denominator_parse
#print axioms geometryRow027_physicalVolume_denominator_nonzero
#print axioms geometryRow027_physicalVolume_parse
#print axioms geometryRow027_physicalVolume_read
#print axioms geometryRow027_meanGap_field
#print axioms geometryRow027_meanGap_numerator_no_slash
#print axioms geometryRow027_meanGap_numerator_parse
#print axioms geometryRow027_meanGap_denominator_parse
#print axioms geometryRow027_meanGap_denominator_nonzero
#print axioms geometryRow027_meanGap_parse
#print axioms geometryRow027_meanGap_read
#print axioms geometryRow027_jensenBound_field
#print axioms geometryRow027_jensenBound_numerator_no_slash
#print axioms geometryRow027_jensenBound_numerator_parse
#print axioms geometryRow027_jensenBound_denominator_parse
#print axioms geometryRow027_jensenBound_denominator_nonzero
#print axioms geometryRow027_jensenBound_parse
#print axioms geometryRow027_jensenBound_read
#print axioms geometryRow027_factorMaxima_read
#print axioms geometryRow027_gapWeightedMeans_read
#print axioms geometryRow027_floor_text_read
#print axioms geometryRow027_floor_chars_parse
#print axioms geometryRow027_floor_parse
#print axioms decode_geometry_Rows_027
#print axioms geometry_Rows_block_013_push_eq
#print axioms geometry_Rows_block_013_reverse
#print axioms decode_geometry_Rows_block_013
#print axioms decode_geometry_Rows_through_block_013

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
