import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows011

/-! Original simplices typed block 12, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson024 : SourceJson :=
  (SimplicesBlock012.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped024 : GeometryRow :=
  { simplexId := 24,
    vertexIds := #[39, 35, 29, 11, 9, 7, 6, 2, 0],
    physicalVolume := ((2019940214900207679169057624705132872449 : ℚ) / (642373543526400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((9233771 : ℚ) / (168000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((5774196571 : ℚ) / (67200000000 : ℚ)), ((40914287677 : ℚ) / (470400000000 : ℚ)), ((6730345357 : ℚ) / (47040000000 : ℚ)), ((160845189401 : ℚ) / (1411200000000 : ℚ)), ((9832379511 : ℚ) / (156800000000 : ℚ)), ((11617172047 : ℚ) / (235200000000 : ℚ)), ((9715259143 : ℚ) / (235200000000 : ℚ)), ((16144956671 : ℚ) / (470400000000 : ℚ)), ((5381631317 : ℚ) / (156800000000 : ℚ)), ((44037463789 : ℚ) / (1411200000000 : ℚ))],
    jensenBound := ((4642934861681259885116353489043433695613543555507928613689648742400000000000000000000000 : ℚ) / (361973935105803154383660355059711151698915826891614645166628550946525107609091763060639939238170597849 : ℚ)),
    jensenFloorQ96 := (1016236701288741 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_simplexId_before"
  err.flush

theorem geometryRow024_simplexId_read :
    geometryRowsJson024.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped024.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_vertexIds_before"
  err.flush

theorem geometryRow024_vertexIds_read :
    geometryRowsJson024.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped024.vertexIds := by decide +kernel

noncomputable def geometryRow024_physicalVolumeNumeratorChars : List Char := ['2', '0', '1', '9', '9', '4', '0', '2', '1', '4', '9', '0', '0', '2', '0', '7', '6', '7', '9', '1', '6', '9', '0', '5', '7', '6', '2', '4', '7', '0', '5', '1', '3', '2', '8', '7', '2', '4', '4', '9']
noncomputable def geometryRow024_physicalVolumeDenominatorChars : List Char := ['6', '4', '2', '3', '7', '3', '5', '4', '3', '5', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_physicalVolumeText : String := String.ofList (geometryRow024_physicalVolumeNumeratorChars ++ '/' :: geometryRow024_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_physicalVolume_before_field"
  err.flush

theorem geometryRow024_physicalVolume_field :
    geometryRowsJson024.getObjVal? "physical_volume" = .ok (.str geometryRow024_physicalVolumeText) := by rfl

theorem geometryRow024_physicalVolume_numerator_no_slash :
    geometryRow024_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow024_physicalVolumeNumeratorChars = some (2019940214900207679169057624705132872449 : Int) := by decide +kernel

theorem geometryRow024_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow024_physicalVolumeDenominatorChars = some (642373543526400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow024_physicalVolume_denominator_nonzero : (642373543526400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_physicalVolume_parse :
    parseRational geometryRow024_physicalVolumeText = .ok geometryRowsTyped024.physicalVolume :=
  original_rational_fraction_of_chars geometryRow024_physicalVolumeNumeratorChars geometryRow024_physicalVolumeDenominatorChars
    (2019940214900207679169057624705132872449 : Int) (642373543526400000000000000000000000000000000000000000000000000 : Int)
    geometryRow024_physicalVolume_numerator_no_slash geometryRow024_physicalVolume_numerator_parse
    geometryRow024_physicalVolume_denominator_parse geometryRow024_physicalVolume_denominator_nonzero

theorem geometryRow024_physicalVolume_read :
    rationalField geometryRowsJson024 "physical_volume" = .ok geometryRowsTyped024.physicalVolume :=
  original_rationalField_of_string geometryRowsJson024 "physical_volume" geometryRow024_physicalVolumeText
    geometryRowsTyped024.physicalVolume geometryRow024_physicalVolume_field geometryRow024_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_physicalVolume_complete"
  err.flush

noncomputable def geometryRow024_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow024_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_meanGapText : String := String.ofList (geometryRow024_meanGapNumeratorChars ++ '/' :: geometryRow024_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_meanGap_before_field"
  err.flush

theorem geometryRow024_meanGap_field :
    geometryRowsJson024.getObjVal? "mean_gap" = .ok (.str geometryRow024_meanGapText) := by rfl

theorem geometryRow024_meanGap_numerator_no_slash :
    geometryRow024_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_meanGap_numerator_parse :
    SourceJson.intChars geometryRow024_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow024_meanGap_denominator_parse :
    SourceJson.intChars geometryRow024_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow024_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_meanGap_parse :
    parseRational geometryRow024_meanGapText = .ok geometryRowsTyped024.meanGap :=
  original_rational_fraction_of_chars geometryRow024_meanGapNumeratorChars geometryRow024_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow024_meanGap_numerator_no_slash geometryRow024_meanGap_numerator_parse
    geometryRow024_meanGap_denominator_parse geometryRow024_meanGap_denominator_nonzero

theorem geometryRow024_meanGap_read :
    rationalField geometryRowsJson024 "mean_gap" = .ok geometryRowsTyped024.meanGap :=
  original_rationalField_of_string geometryRowsJson024 "mean_gap" geometryRow024_meanGapText
    geometryRowsTyped024.meanGap geometryRow024_meanGap_field geometryRow024_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_meanGap_complete"
  err.flush

noncomputable def geometryRow024_jensenBoundNumeratorChars : List Char := ['4', '6', '4', '2', '9', '3', '4', '8', '6', '1', '6', '8', '1', '2', '5', '9', '8', '8', '5', '1', '1', '6', '3', '5', '3', '4', '8', '9', '0', '4', '3', '4', '3', '3', '6', '9', '5', '6', '1', '3', '5', '4', '3', '5', '5', '5', '5', '0', '7', '9', '2', '8', '6', '1', '3', '6', '8', '9', '6', '4', '8', '7', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_jensenBoundDenominatorChars : List Char := ['3', '6', '1', '9', '7', '3', '9', '3', '5', '1', '0', '5', '8', '0', '3', '1', '5', '4', '3', '8', '3', '6', '6', '0', '3', '5', '5', '0', '5', '9', '7', '1', '1', '1', '5', '1', '6', '9', '8', '9', '1', '5', '8', '2', '6', '8', '9', '1', '6', '1', '4', '6', '4', '5', '1', '6', '6', '6', '2', '8', '5', '5', '0', '9', '4', '6', '5', '2', '5', '1', '0', '7', '6', '0', '9', '0', '9', '1', '7', '6', '3', '0', '6', '0', '6', '3', '9', '9', '3', '9', '2', '3', '8', '1', '7', '0', '5', '9', '7', '8', '4', '9']
noncomputable def geometryRow024_jensenBoundText : String := String.ofList (geometryRow024_jensenBoundNumeratorChars ++ '/' :: geometryRow024_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_jensenBound_before_field"
  err.flush

theorem geometryRow024_jensenBound_field :
    geometryRowsJson024.getObjVal? "jensen_bound" = .ok (.str geometryRow024_jensenBoundText) := by rfl

theorem geometryRow024_jensenBound_numerator_no_slash :
    geometryRow024_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow024_jensenBoundNumeratorChars = some (4642934861681259885116353489043433695613543555507928613689648742400000000000000000000000 : Int) := by decide +kernel

theorem geometryRow024_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow024_jensenBoundDenominatorChars = some (361973935105803154383660355059711151698915826891614645166628550946525107609091763060639939238170597849 : Int) := by decide +kernel

theorem geometryRow024_jensenBound_denominator_nonzero : (361973935105803154383660355059711151698915826891614645166628550946525107609091763060639939238170597849 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_jensenBound_parse :
    parseRational geometryRow024_jensenBoundText = .ok geometryRowsTyped024.jensenBound :=
  original_rational_fraction_of_chars geometryRow024_jensenBoundNumeratorChars geometryRow024_jensenBoundDenominatorChars
    (4642934861681259885116353489043433695613543555507928613689648742400000000000000000000000 : Int) (361973935105803154383660355059711151698915826891614645166628550946525107609091763060639939238170597849 : Int)
    geometryRow024_jensenBound_numerator_no_slash geometryRow024_jensenBound_numerator_parse
    geometryRow024_jensenBound_denominator_parse geometryRow024_jensenBound_denominator_nonzero

theorem geometryRow024_jensenBound_read :
    rationalField geometryRowsJson024 "jensen_bound" = .ok geometryRowsTyped024.jensenBound :=
  original_rationalField_of_string geometryRowsJson024 "jensen_bound" geometryRow024_jensenBoundText
    geometryRowsTyped024.jensenBound geometryRow024_jensenBound_field geometryRow024_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_factorMaxima_before"
  err.flush

theorem geometryRow024_factorMaxima_read :
    rationalArrayField geometryRowsJson024 "factor_maxima" = .ok geometryRowsTyped024.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_gapWeightedMeans_before"
  err.flush

theorem geometryRow024_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson024 "gap_weighted_means" = .ok geometryRowsTyped024.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow024_floorChars : List Char := ['1', '0', '1', '6', '2', '3', '6', '7', '0', '1', '2', '8', '8', '7', '4', '1']
noncomputable def geometryRow024_floorText : String := String.ofList geometryRow024_floorChars

theorem geometryRow024_floor_text_read :
    geometryRowsJson024.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow024_floorText := by rfl

theorem geometryRow024_floor_chars_parse :
    SourceJson.intChars geometryRow024_floorChars = some (1016236701288741 : Int) := by decide +kernel

theorem geometryRow024_floor_parse :
    parseInteger geometryRow024_floorText = .ok geometryRowsTyped024.jensenFloorQ96 := by
  simp only [geometryRow024_floorText, parseInteger, String.toList_ofList, geometryRow024_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_024 :
    decodeGeometryRow geometryRowsJson024 = .ok geometryRowsTyped024 :=
  original_geometryRow_of_fields geometryRowsJson024 geometryRowsTyped024 geometryRow024_floorText
    geometryRow024_simplexId_read geometryRow024_vertexIds_read
    geometryRow024_physicalVolume_read geometryRow024_meanGap_read
    geometryRow024_factorMaxima_read geometryRow024_gapWeightedMeans_read
    geometryRow024_jensenBound_read geometryRow024_floor_text_read geometryRow024_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_024_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson025 : SourceJson :=
  (SimplicesBlock012.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped025 : GeometryRow :=
  { simplexId := 25,
    vertexIds := #[39, 35, 29, 27, 26, 17, 12, 2, 0],
    physicalVolume := ((4351376819998706033464094224371101159369 : ℚ) / (1922362308034560000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2784283 : ℚ) / (33600000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546639 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((281164649719 : ℚ) / (3393600000000 : ℚ)), ((1993145587873 : ℚ) / (23755200000000 : ℚ)), ((1725348002501 : ℚ) / (11877600000000 : ℚ)), ((8351322803717 : ℚ) / (71265600000000 : ℚ)), ((1672140139981 : ℚ) / (23755200000000 : ℚ)), ((561671012179 : ℚ) / (11877600000000 : ℚ)), ((441118298029 : ℚ) / (11877600000000 : ℚ)), ((783661844923 : ℚ) / (23755200000000 : ℚ)), ((261220087081 : ℚ) / (7918400000000 : ℚ)), ((2150865981529 : ℚ) / (71265600000000 : ℚ))],
    jensenBound := ((438488030976157305503873668016177917298755775501211678558644224585665886623498240000000000000000000000000 : ℚ) / (39809651009090442701416067877816531169032402692285922150529813339322252356255801910039871303086899939976458666776724939 : ℚ)),
    jensenFloorQ96 := (872667810396173 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_simplexId_before"
  err.flush

theorem geometryRow025_simplexId_read :
    geometryRowsJson025.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped025.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_vertexIds_before"
  err.flush

theorem geometryRow025_vertexIds_read :
    geometryRowsJson025.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped025.vertexIds := by decide +kernel

noncomputable def geometryRow025_physicalVolumeNumeratorChars : List Char := ['4', '3', '5', '1', '3', '7', '6', '8', '1', '9', '9', '9', '8', '7', '0', '6', '0', '3', '3', '4', '6', '4', '0', '9', '4', '2', '2', '4', '3', '7', '1', '1', '0', '1', '1', '5', '9', '3', '6', '9']
noncomputable def geometryRow025_physicalVolumeDenominatorChars : List Char := ['1', '9', '2', '2', '3', '6', '2', '3', '0', '8', '0', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_physicalVolumeText : String := String.ofList (geometryRow025_physicalVolumeNumeratorChars ++ '/' :: geometryRow025_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_physicalVolume_before_field"
  err.flush

theorem geometryRow025_physicalVolume_field :
    geometryRowsJson025.getObjVal? "physical_volume" = .ok (.str geometryRow025_physicalVolumeText) := by rfl

theorem geometryRow025_physicalVolume_numerator_no_slash :
    geometryRow025_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow025_physicalVolumeNumeratorChars = some (4351376819998706033464094224371101159369 : Int) := by decide +kernel

theorem geometryRow025_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow025_physicalVolumeDenominatorChars = some (1922362308034560000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow025_physicalVolume_denominator_nonzero : (1922362308034560000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_physicalVolume_parse :
    parseRational geometryRow025_physicalVolumeText = .ok geometryRowsTyped025.physicalVolume :=
  original_rational_fraction_of_chars geometryRow025_physicalVolumeNumeratorChars geometryRow025_physicalVolumeDenominatorChars
    (4351376819998706033464094224371101159369 : Int) (1922362308034560000000000000000000000000000000000000000000000000 : Int)
    geometryRow025_physicalVolume_numerator_no_slash geometryRow025_physicalVolume_numerator_parse
    geometryRow025_physicalVolume_denominator_parse geometryRow025_physicalVolume_denominator_nonzero

theorem geometryRow025_physicalVolume_read :
    rationalField geometryRowsJson025 "physical_volume" = .ok geometryRowsTyped025.physicalVolume :=
  original_rationalField_of_string geometryRowsJson025 "physical_volume" geometryRow025_physicalVolumeText
    geometryRowsTyped025.physicalVolume geometryRow025_physicalVolume_field geometryRow025_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_physicalVolume_complete"
  err.flush

noncomputable def geometryRow025_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow025_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_meanGapText : String := String.ofList (geometryRow025_meanGapNumeratorChars ++ '/' :: geometryRow025_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_meanGap_before_field"
  err.flush

theorem geometryRow025_meanGap_field :
    geometryRowsJson025.getObjVal? "mean_gap" = .ok (.str geometryRow025_meanGapText) := by rfl

theorem geometryRow025_meanGap_numerator_no_slash :
    geometryRow025_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_meanGap_numerator_parse :
    SourceJson.intChars geometryRow025_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow025_meanGap_denominator_parse :
    SourceJson.intChars geometryRow025_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow025_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_meanGap_parse :
    parseRational geometryRow025_meanGapText = .ok geometryRowsTyped025.meanGap :=
  original_rational_fraction_of_chars geometryRow025_meanGapNumeratorChars geometryRow025_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow025_meanGap_numerator_no_slash geometryRow025_meanGap_numerator_parse
    geometryRow025_meanGap_denominator_parse geometryRow025_meanGap_denominator_nonzero

theorem geometryRow025_meanGap_read :
    rationalField geometryRowsJson025 "mean_gap" = .ok geometryRowsTyped025.meanGap :=
  original_rationalField_of_string geometryRowsJson025 "mean_gap" geometryRow025_meanGapText
    geometryRowsTyped025.meanGap geometryRow025_meanGap_field geometryRow025_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_meanGap_complete"
  err.flush

noncomputable def geometryRow025_jensenBoundNumeratorChars : List Char := ['4', '3', '8', '4', '8', '8', '0', '3', '0', '9', '7', '6', '1', '5', '7', '3', '0', '5', '5', '0', '3', '8', '7', '3', '6', '6', '8', '0', '1', '6', '1', '7', '7', '9', '1', '7', '2', '9', '8', '7', '5', '5', '7', '7', '5', '5', '0', '1', '2', '1', '1', '6', '7', '8', '5', '5', '8', '6', '4', '4', '2', '2', '4', '5', '8', '5', '6', '6', '5', '8', '8', '6', '6', '2', '3', '4', '9', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_jensenBoundDenominatorChars : List Char := ['3', '9', '8', '0', '9', '6', '5', '1', '0', '0', '9', '0', '9', '0', '4', '4', '2', '7', '0', '1', '4', '1', '6', '0', '6', '7', '8', '7', '7', '8', '1', '6', '5', '3', '1', '1', '6', '9', '0', '3', '2', '4', '0', '2', '6', '9', '2', '2', '8', '5', '9', '2', '2', '1', '5', '0', '5', '2', '9', '8', '1', '3', '3', '3', '9', '3', '2', '2', '2', '5', '2', '3', '5', '6', '2', '5', '5', '8', '0', '1', '9', '1', '0', '0', '3', '9', '8', '7', '1', '3', '0', '3', '0', '8', '6', '8', '9', '9', '9', '3', '9', '9', '7', '6', '4', '5', '8', '6', '6', '6', '7', '7', '6', '7', '2', '4', '9', '3', '9']
noncomputable def geometryRow025_jensenBoundText : String := String.ofList (geometryRow025_jensenBoundNumeratorChars ++ '/' :: geometryRow025_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_jensenBound_before_field"
  err.flush

theorem geometryRow025_jensenBound_field :
    geometryRowsJson025.getObjVal? "jensen_bound" = .ok (.str geometryRow025_jensenBoundText) := by rfl

theorem geometryRow025_jensenBound_numerator_no_slash :
    geometryRow025_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow025_jensenBoundNumeratorChars = some (438488030976157305503873668016177917298755775501211678558644224585665886623498240000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow025_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow025_jensenBoundDenominatorChars = some (39809651009090442701416067877816531169032402692285922150529813339322252356255801910039871303086899939976458666776724939 : Int) := by decide +kernel

theorem geometryRow025_jensenBound_denominator_nonzero : (39809651009090442701416067877816531169032402692285922150529813339322252356255801910039871303086899939976458666776724939 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_jensenBound_parse :
    parseRational geometryRow025_jensenBoundText = .ok geometryRowsTyped025.jensenBound :=
  original_rational_fraction_of_chars geometryRow025_jensenBoundNumeratorChars geometryRow025_jensenBoundDenominatorChars
    (438488030976157305503873668016177917298755775501211678558644224585665886623498240000000000000000000000000 : Int) (39809651009090442701416067877816531169032402692285922150529813339322252356255801910039871303086899939976458666776724939 : Int)
    geometryRow025_jensenBound_numerator_no_slash geometryRow025_jensenBound_numerator_parse
    geometryRow025_jensenBound_denominator_parse geometryRow025_jensenBound_denominator_nonzero

theorem geometryRow025_jensenBound_read :
    rationalField geometryRowsJson025 "jensen_bound" = .ok geometryRowsTyped025.jensenBound :=
  original_rationalField_of_string geometryRowsJson025 "jensen_bound" geometryRow025_jensenBoundText
    geometryRowsTyped025.jensenBound geometryRow025_jensenBound_field geometryRow025_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_factorMaxima_before"
  err.flush

theorem geometryRow025_factorMaxima_read :
    rationalArrayField geometryRowsJson025 "factor_maxima" = .ok geometryRowsTyped025.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_gapWeightedMeans_before"
  err.flush

theorem geometryRow025_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson025 "gap_weighted_means" = .ok geometryRowsTyped025.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow025_floorChars : List Char := ['8', '7', '2', '6', '6', '7', '8', '1', '0', '3', '9', '6', '1', '7', '3']
noncomputable def geometryRow025_floorText : String := String.ofList geometryRow025_floorChars

theorem geometryRow025_floor_text_read :
    geometryRowsJson025.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow025_floorText := by rfl

theorem geometryRow025_floor_chars_parse :
    SourceJson.intChars geometryRow025_floorChars = some (872667810396173 : Int) := by decide +kernel

theorem geometryRow025_floor_parse :
    parseInteger geometryRow025_floorText = .ok geometryRowsTyped025.jensenFloorQ96 := by
  simp only [geometryRow025_floorText, parseInteger, String.toList_ofList, geometryRow025_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_025 :
    decodeGeometryRow geometryRowsJson025 = .ok geometryRowsTyped025 :=
  original_geometryRow_of_fields geometryRowsJson025 geometryRowsTyped025 geometryRow025_floorText
    geometryRow025_simplexId_read geometryRow025_vertexIds_read
    geometryRow025_physicalVolume_read geometryRow025_meanGap_read
    geometryRow025_factorMaxima_read geometryRow025_gapWeightedMeans_read
    geometryRow025_jensenBound_read geometryRow025_floor_text_read geometryRow025_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_025_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock012 : List SourceJson := [geometryRowsJson024, geometryRowsJson025]
noncomputable def geometryRowsTypedBlock012 : List (GeometryRow) := [geometryRowsTyped024, geometryRowsTyped025]
noncomputable def geometryRowsTypedThroughBlock012 : List (GeometryRow) := geometryRowsTypedThroughBlock011 ++ geometryRowsTypedBlock012

theorem geometry_Rows_block_012_push_eq (acc : List SourceJson) :
    SimplicesBlock012.blockPush acc = [geometryRowsJson025, geometryRowsJson024] ++ acc := by rfl

theorem geometry_Rows_block_012_reverse (acc : List SourceJson) :
    (SimplicesBlock012.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock012 := by
  rw [geometry_Rows_block_012_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_012 :
    geometryRowsJsonBlock012.mapM decodeGeometryRow = .ok geometryRowsTypedBlock012 := by
  simp only [geometryRowsJsonBlock012, geometryRowsTypedBlock012, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_024, decode_geometry_Rows_025]
  rfl

theorem decode_geometry_Rows_through_block_012 :
    SimplicesValue.arrayAcc013.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock012 := by
  change (SimplicesBlock012.blockPush SimplicesValue.arrayAcc012).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_012_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_011, decode_geometry_Rows_block_012]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_012_complete"
  err.flush

#print axioms geometryRow024_simplexId_read
#print axioms geometryRow024_vertexIds_read
#print axioms geometryRow024_physicalVolume_field
#print axioms geometryRow024_physicalVolume_numerator_no_slash
#print axioms geometryRow024_physicalVolume_numerator_parse
#print axioms geometryRow024_physicalVolume_denominator_parse
#print axioms geometryRow024_physicalVolume_denominator_nonzero
#print axioms geometryRow024_physicalVolume_parse
#print axioms geometryRow024_physicalVolume_read
#print axioms geometryRow024_meanGap_field
#print axioms geometryRow024_meanGap_numerator_no_slash
#print axioms geometryRow024_meanGap_numerator_parse
#print axioms geometryRow024_meanGap_denominator_parse
#print axioms geometryRow024_meanGap_denominator_nonzero
#print axioms geometryRow024_meanGap_parse
#print axioms geometryRow024_meanGap_read
#print axioms geometryRow024_jensenBound_field
#print axioms geometryRow024_jensenBound_numerator_no_slash
#print axioms geometryRow024_jensenBound_numerator_parse
#print axioms geometryRow024_jensenBound_denominator_parse
#print axioms geometryRow024_jensenBound_denominator_nonzero
#print axioms geometryRow024_jensenBound_parse
#print axioms geometryRow024_jensenBound_read
#print axioms geometryRow024_factorMaxima_read
#print axioms geometryRow024_gapWeightedMeans_read
#print axioms geometryRow024_floor_text_read
#print axioms geometryRow024_floor_chars_parse
#print axioms geometryRow024_floor_parse
#print axioms decode_geometry_Rows_024
#print axioms geometryRow025_simplexId_read
#print axioms geometryRow025_vertexIds_read
#print axioms geometryRow025_physicalVolume_field
#print axioms geometryRow025_physicalVolume_numerator_no_slash
#print axioms geometryRow025_physicalVolume_numerator_parse
#print axioms geometryRow025_physicalVolume_denominator_parse
#print axioms geometryRow025_physicalVolume_denominator_nonzero
#print axioms geometryRow025_physicalVolume_parse
#print axioms geometryRow025_physicalVolume_read
#print axioms geometryRow025_meanGap_field
#print axioms geometryRow025_meanGap_numerator_no_slash
#print axioms geometryRow025_meanGap_numerator_parse
#print axioms geometryRow025_meanGap_denominator_parse
#print axioms geometryRow025_meanGap_denominator_nonzero
#print axioms geometryRow025_meanGap_parse
#print axioms geometryRow025_meanGap_read
#print axioms geometryRow025_jensenBound_field
#print axioms geometryRow025_jensenBound_numerator_no_slash
#print axioms geometryRow025_jensenBound_numerator_parse
#print axioms geometryRow025_jensenBound_denominator_parse
#print axioms geometryRow025_jensenBound_denominator_nonzero
#print axioms geometryRow025_jensenBound_parse
#print axioms geometryRow025_jensenBound_read
#print axioms geometryRow025_factorMaxima_read
#print axioms geometryRow025_gapWeightedMeans_read
#print axioms geometryRow025_floor_text_read
#print axioms geometryRow025_floor_chars_parse
#print axioms geometryRow025_floor_parse
#print axioms decode_geometry_Rows_025
#print axioms geometry_Rows_block_012_push_eq
#print axioms geometry_Rows_block_012_reverse
#print axioms decode_geometry_Rows_block_012
#print axioms decode_geometry_Rows_through_block_012

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
