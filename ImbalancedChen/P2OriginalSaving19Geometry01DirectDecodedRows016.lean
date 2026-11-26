import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows015

/-! Original simplices typed block 16, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson032 : SourceJson :=
  (SimplicesBlock016.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped032 : GeometryRow :=
  { simplexId := 32,
    vertexIds := #[39, 35, 24, 11, 10, 8, 6, 2, 0],
    physicalVolume := ((6955265400155281998566315890125561139 : ℚ) / (131328000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((178405124329 : ℚ) / (2074800000000 : ℚ)), ((1264116268423 : ℚ) / (14523600000000 : ℚ)), ((95719751773 : ℚ) / (670320000000 : ℚ)), ((269742392973 : ℚ) / (2420600000000 : ℚ)), ((2638039235641 : ℚ) / (43570800000000 : ℚ)), ((2135482193443 : ℚ) / (43570800000000 : ℚ)), ((1753670208587 : ℚ) / (43570800000000 : ℚ)), ((1623442858607 : ℚ) / (43570800000000 : ℚ)), ((1531553661347 : ℚ) / (43570800000000 : ℚ)), ((1458190322051 : ℚ) / (43570800000000 : ℚ))],
    jensenBound := ((4809265293840344721142284978769779959024108947643106926217981426399591095635186237440000000000000000000000 : ℚ) / (24215822970007607547385496748594996827444615348416926519382644491836297701591922630620797473478709128806228124989589 : ℚ)),
    jensenFloorQ96 := (15734722406358686793 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_simplexId_before"
  err.flush

theorem geometryRow032_simplexId_read :
    geometryRowsJson032.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped032.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_vertexIds_before"
  err.flush

theorem geometryRow032_vertexIds_read :
    geometryRowsJson032.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped032.vertexIds := by decide +kernel

noncomputable def geometryRow032_physicalVolumeNumeratorChars : List Char := ['6', '9', '5', '5', '2', '6', '5', '4', '0', '0', '1', '5', '5', '2', '8', '1', '9', '9', '8', '5', '6', '6', '3', '1', '5', '8', '9', '0', '1', '2', '5', '5', '6', '1', '1', '3', '9']
noncomputable def geometryRow032_physicalVolumeDenominatorChars : List Char := ['1', '3', '1', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_physicalVolumeText : String := String.ofList (geometryRow032_physicalVolumeNumeratorChars ++ '/' :: geometryRow032_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_physicalVolume_before_field"
  err.flush

theorem geometryRow032_physicalVolume_field :
    geometryRowsJson032.getObjVal? "physical_volume" = .ok (.str geometryRow032_physicalVolumeText) := by rfl

theorem geometryRow032_physicalVolume_numerator_no_slash :
    geometryRow032_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow032_physicalVolumeNumeratorChars = some (6955265400155281998566315890125561139 : Int) := by decide +kernel

theorem geometryRow032_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow032_physicalVolumeDenominatorChars = some (131328000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow032_physicalVolume_denominator_nonzero : (131328000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_physicalVolume_parse :
    parseRational geometryRow032_physicalVolumeText = .ok geometryRowsTyped032.physicalVolume :=
  original_rational_fraction_of_chars geometryRow032_physicalVolumeNumeratorChars geometryRow032_physicalVolumeDenominatorChars
    (6955265400155281998566315890125561139 : Int) (131328000000000000000000000000000000000000000000000000000 : Int)
    geometryRow032_physicalVolume_numerator_no_slash geometryRow032_physicalVolume_numerator_parse
    geometryRow032_physicalVolume_denominator_parse geometryRow032_physicalVolume_denominator_nonzero

theorem geometryRow032_physicalVolume_read :
    rationalField geometryRowsJson032 "physical_volume" = .ok geometryRowsTyped032.physicalVolume :=
  original_rationalField_of_string geometryRowsJson032 "physical_volume" geometryRow032_physicalVolumeText
    geometryRowsTyped032.physicalVolume geometryRow032_physicalVolume_field geometryRow032_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_physicalVolume_complete"
  err.flush

noncomputable def geometryRow032_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow032_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_meanGapText : String := String.ofList (geometryRow032_meanGapNumeratorChars ++ '/' :: geometryRow032_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_meanGap_before_field"
  err.flush

theorem geometryRow032_meanGap_field :
    geometryRowsJson032.getObjVal? "mean_gap" = .ok (.str geometryRow032_meanGapText) := by rfl

theorem geometryRow032_meanGap_numerator_no_slash :
    geometryRow032_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_meanGap_numerator_parse :
    SourceJson.intChars geometryRow032_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow032_meanGap_denominator_parse :
    SourceJson.intChars geometryRow032_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow032_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_meanGap_parse :
    parseRational geometryRow032_meanGapText = .ok geometryRowsTyped032.meanGap :=
  original_rational_fraction_of_chars geometryRow032_meanGapNumeratorChars geometryRow032_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow032_meanGap_numerator_no_slash geometryRow032_meanGap_numerator_parse
    geometryRow032_meanGap_denominator_parse geometryRow032_meanGap_denominator_nonzero

theorem geometryRow032_meanGap_read :
    rationalField geometryRowsJson032 "mean_gap" = .ok geometryRowsTyped032.meanGap :=
  original_rationalField_of_string geometryRowsJson032 "mean_gap" geometryRow032_meanGapText
    geometryRowsTyped032.meanGap geometryRow032_meanGap_field geometryRow032_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_meanGap_complete"
  err.flush

noncomputable def geometryRow032_jensenBoundNumeratorChars : List Char := ['4', '8', '0', '9', '2', '6', '5', '2', '9', '3', '8', '4', '0', '3', '4', '4', '7', '2', '1', '1', '4', '2', '2', '8', '4', '9', '7', '8', '7', '6', '9', '7', '7', '9', '9', '5', '9', '0', '2', '4', '1', '0', '8', '9', '4', '7', '6', '4', '3', '1', '0', '6', '9', '2', '6', '2', '1', '7', '9', '8', '1', '4', '2', '6', '3', '9', '9', '5', '9', '1', '0', '9', '5', '6', '3', '5', '1', '8', '6', '2', '3', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_jensenBoundDenominatorChars : List Char := ['2', '4', '2', '1', '5', '8', '2', '2', '9', '7', '0', '0', '0', '7', '6', '0', '7', '5', '4', '7', '3', '8', '5', '4', '9', '6', '7', '4', '8', '5', '9', '4', '9', '9', '6', '8', '2', '7', '4', '4', '4', '6', '1', '5', '3', '4', '8', '4', '1', '6', '9', '2', '6', '5', '1', '9', '3', '8', '2', '6', '4', '4', '4', '9', '1', '8', '3', '6', '2', '9', '7', '7', '0', '1', '5', '9', '1', '9', '2', '2', '6', '3', '0', '6', '2', '0', '7', '9', '7', '4', '7', '3', '4', '7', '8', '7', '0', '9', '1', '2', '8', '8', '0', '6', '2', '2', '8', '1', '2', '4', '9', '8', '9', '5', '8', '9']
noncomputable def geometryRow032_jensenBoundText : String := String.ofList (geometryRow032_jensenBoundNumeratorChars ++ '/' :: geometryRow032_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_jensenBound_before_field"
  err.flush

theorem geometryRow032_jensenBound_field :
    geometryRowsJson032.getObjVal? "jensen_bound" = .ok (.str geometryRow032_jensenBoundText) := by rfl

theorem geometryRow032_jensenBound_numerator_no_slash :
    geometryRow032_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow032_jensenBoundNumeratorChars = some (4809265293840344721142284978769779959024108947643106926217981426399591095635186237440000000000000000000000 : Int) := by decide +kernel

theorem geometryRow032_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow032_jensenBoundDenominatorChars = some (24215822970007607547385496748594996827444615348416926519382644491836297701591922630620797473478709128806228124989589 : Int) := by decide +kernel

theorem geometryRow032_jensenBound_denominator_nonzero : (24215822970007607547385496748594996827444615348416926519382644491836297701591922630620797473478709128806228124989589 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_jensenBound_parse :
    parseRational geometryRow032_jensenBoundText = .ok geometryRowsTyped032.jensenBound :=
  original_rational_fraction_of_chars geometryRow032_jensenBoundNumeratorChars geometryRow032_jensenBoundDenominatorChars
    (4809265293840344721142284978769779959024108947643106926217981426399591095635186237440000000000000000000000 : Int) (24215822970007607547385496748594996827444615348416926519382644491836297701591922630620797473478709128806228124989589 : Int)
    geometryRow032_jensenBound_numerator_no_slash geometryRow032_jensenBound_numerator_parse
    geometryRow032_jensenBound_denominator_parse geometryRow032_jensenBound_denominator_nonzero

theorem geometryRow032_jensenBound_read :
    rationalField geometryRowsJson032 "jensen_bound" = .ok geometryRowsTyped032.jensenBound :=
  original_rationalField_of_string geometryRowsJson032 "jensen_bound" geometryRow032_jensenBoundText
    geometryRowsTyped032.jensenBound geometryRow032_jensenBound_field geometryRow032_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_factorMaxima_before"
  err.flush

theorem geometryRow032_factorMaxima_read :
    rationalArrayField geometryRowsJson032 "factor_maxima" = .ok geometryRowsTyped032.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_gapWeightedMeans_before"
  err.flush

theorem geometryRow032_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson032 "gap_weighted_means" = .ok geometryRowsTyped032.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow032_floorChars : List Char := ['1', '5', '7', '3', '4', '7', '2', '2', '4', '0', '6', '3', '5', '8', '6', '8', '6', '7', '9', '3']
noncomputable def geometryRow032_floorText : String := String.ofList geometryRow032_floorChars

theorem geometryRow032_floor_text_read :
    geometryRowsJson032.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow032_floorText := by rfl

theorem geometryRow032_floor_chars_parse :
    SourceJson.intChars geometryRow032_floorChars = some (15734722406358686793 : Int) := by decide +kernel

theorem geometryRow032_floor_parse :
    parseInteger geometryRow032_floorText = .ok geometryRowsTyped032.jensenFloorQ96 := by
  simp only [geometryRow032_floorText, parseInteger, String.toList_ofList, geometryRow032_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_032 :
    decodeGeometryRow geometryRowsJson032 = .ok geometryRowsTyped032 :=
  original_geometryRow_of_fields geometryRowsJson032 geometryRowsTyped032 geometryRow032_floorText
    geometryRow032_simplexId_read geometryRow032_vertexIds_read
    geometryRow032_physicalVolume_read geometryRow032_meanGap_read
    geometryRow032_factorMaxima_read geometryRow032_gapWeightedMeans_read
    geometryRow032_jensenBound_read geometryRow032_floor_text_read geometryRow032_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_032_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson033 : SourceJson :=
  (SimplicesBlock016.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped033 : GeometryRow :=
  { simplexId := 33,
    vertexIds := #[39, 35, 24, 11, 10, 7, 6, 2, 0],
    physicalVolume := ((1913951768112163157310923331101138906565323 : ℚ) / (22239608832000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((13512492793 : ℚ) / (159600000000 : ℚ)), ((95762864791 : ℚ) / (1117200000000 : ℚ)), ((10635527561 : ℚ) / (74480000000 : ℚ)), ((187483148369 : ℚ) / (1675800000000 : ℚ)), ((67395905839 : ℚ) / (1117200000000 : ℚ)), ((18498118679 : ℚ) / (372400000000 : ℚ)), ((15029654201 : ℚ) / (372400000000 : ℚ)), ((41749799783 : ℚ) / (1117200000000 : ℚ)), ((40378269203 : ℚ) / (1117200000000 : ℚ)), ((110691638147 : ℚ) / (3351600000000 : ℚ))],
    jensenBound := ((263845087152685016050480649314895477685476863897660729273165976776556146560000000000000000000000 : ℚ) / (820140334435874266915193800869516911316263523032777500425290296414193700538685303063129806311707886781771 : ℚ)),
    jensenFloorQ96 := (25488273854866261798 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_simplexId_before"
  err.flush

theorem geometryRow033_simplexId_read :
    geometryRowsJson033.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped033.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_vertexIds_before"
  err.flush

theorem geometryRow033_vertexIds_read :
    geometryRowsJson033.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped033.vertexIds := by decide +kernel

noncomputable def geometryRow033_physicalVolumeNumeratorChars : List Char := ['1', '9', '1', '3', '9', '5', '1', '7', '6', '8', '1', '1', '2', '1', '6', '3', '1', '5', '7', '3', '1', '0', '9', '2', '3', '3', '3', '1', '1', '0', '1', '1', '3', '8', '9', '0', '6', '5', '6', '5', '3', '2', '3']
noncomputable def geometryRow033_physicalVolumeDenominatorChars : List Char := ['2', '2', '2', '3', '9', '6', '0', '8', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_physicalVolumeText : String := String.ofList (geometryRow033_physicalVolumeNumeratorChars ++ '/' :: geometryRow033_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_physicalVolume_before_field"
  err.flush

theorem geometryRow033_physicalVolume_field :
    geometryRowsJson033.getObjVal? "physical_volume" = .ok (.str geometryRow033_physicalVolumeText) := by rfl

theorem geometryRow033_physicalVolume_numerator_no_slash :
    geometryRow033_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow033_physicalVolumeNumeratorChars = some (1913951768112163157310923331101138906565323 : Int) := by decide +kernel

theorem geometryRow033_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow033_physicalVolumeDenominatorChars = some (22239608832000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow033_physicalVolume_denominator_nonzero : (22239608832000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_physicalVolume_parse :
    parseRational geometryRow033_physicalVolumeText = .ok geometryRowsTyped033.physicalVolume :=
  original_rational_fraction_of_chars geometryRow033_physicalVolumeNumeratorChars geometryRow033_physicalVolumeDenominatorChars
    (1913951768112163157310923331101138906565323 : Int) (22239608832000000000000000000000000000000000000000000000000000 : Int)
    geometryRow033_physicalVolume_numerator_no_slash geometryRow033_physicalVolume_numerator_parse
    geometryRow033_physicalVolume_denominator_parse geometryRow033_physicalVolume_denominator_nonzero

theorem geometryRow033_physicalVolume_read :
    rationalField geometryRowsJson033 "physical_volume" = .ok geometryRowsTyped033.physicalVolume :=
  original_rationalField_of_string geometryRowsJson033 "physical_volume" geometryRow033_physicalVolumeText
    geometryRowsTyped033.physicalVolume geometryRow033_physicalVolume_field geometryRow033_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_physicalVolume_complete"
  err.flush

noncomputable def geometryRow033_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow033_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_meanGapText : String := String.ofList (geometryRow033_meanGapNumeratorChars ++ '/' :: geometryRow033_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_meanGap_before_field"
  err.flush

theorem geometryRow033_meanGap_field :
    geometryRowsJson033.getObjVal? "mean_gap" = .ok (.str geometryRow033_meanGapText) := by rfl

theorem geometryRow033_meanGap_numerator_no_slash :
    geometryRow033_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_meanGap_numerator_parse :
    SourceJson.intChars geometryRow033_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow033_meanGap_denominator_parse :
    SourceJson.intChars geometryRow033_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow033_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_meanGap_parse :
    parseRational geometryRow033_meanGapText = .ok geometryRowsTyped033.meanGap :=
  original_rational_fraction_of_chars geometryRow033_meanGapNumeratorChars geometryRow033_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow033_meanGap_numerator_no_slash geometryRow033_meanGap_numerator_parse
    geometryRow033_meanGap_denominator_parse geometryRow033_meanGap_denominator_nonzero

theorem geometryRow033_meanGap_read :
    rationalField geometryRowsJson033 "mean_gap" = .ok geometryRowsTyped033.meanGap :=
  original_rationalField_of_string geometryRowsJson033 "mean_gap" geometryRow033_meanGapText
    geometryRowsTyped033.meanGap geometryRow033_meanGap_field geometryRow033_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_meanGap_complete"
  err.flush

noncomputable def geometryRow033_jensenBoundNumeratorChars : List Char := ['2', '6', '3', '8', '4', '5', '0', '8', '7', '1', '5', '2', '6', '8', '5', '0', '1', '6', '0', '5', '0', '4', '8', '0', '6', '4', '9', '3', '1', '4', '8', '9', '5', '4', '7', '7', '6', '8', '5', '4', '7', '6', '8', '6', '3', '8', '9', '7', '6', '6', '0', '7', '2', '9', '2', '7', '3', '1', '6', '5', '9', '7', '6', '7', '7', '6', '5', '5', '6', '1', '4', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_jensenBoundDenominatorChars : List Char := ['8', '2', '0', '1', '4', '0', '3', '3', '4', '4', '3', '5', '8', '7', '4', '2', '6', '6', '9', '1', '5', '1', '9', '3', '8', '0', '0', '8', '6', '9', '5', '1', '6', '9', '1', '1', '3', '1', '6', '2', '6', '3', '5', '2', '3', '0', '3', '2', '7', '7', '7', '5', '0', '0', '4', '2', '5', '2', '9', '0', '2', '9', '6', '4', '1', '4', '1', '9', '3', '7', '0', '0', '5', '3', '8', '6', '8', '5', '3', '0', '3', '0', '6', '3', '1', '2', '9', '8', '0', '6', '3', '1', '1', '7', '0', '7', '8', '8', '6', '7', '8', '1', '7', '7', '1']
noncomputable def geometryRow033_jensenBoundText : String := String.ofList (geometryRow033_jensenBoundNumeratorChars ++ '/' :: geometryRow033_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_jensenBound_before_field"
  err.flush

theorem geometryRow033_jensenBound_field :
    geometryRowsJson033.getObjVal? "jensen_bound" = .ok (.str geometryRow033_jensenBoundText) := by rfl

theorem geometryRow033_jensenBound_numerator_no_slash :
    geometryRow033_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow033_jensenBoundNumeratorChars = some (263845087152685016050480649314895477685476863897660729273165976776556146560000000000000000000000 : Int) := by decide +kernel

theorem geometryRow033_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow033_jensenBoundDenominatorChars = some (820140334435874266915193800869516911316263523032777500425290296414193700538685303063129806311707886781771 : Int) := by decide +kernel

theorem geometryRow033_jensenBound_denominator_nonzero : (820140334435874266915193800869516911316263523032777500425290296414193700538685303063129806311707886781771 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_jensenBound_parse :
    parseRational geometryRow033_jensenBoundText = .ok geometryRowsTyped033.jensenBound :=
  original_rational_fraction_of_chars geometryRow033_jensenBoundNumeratorChars geometryRow033_jensenBoundDenominatorChars
    (263845087152685016050480649314895477685476863897660729273165976776556146560000000000000000000000 : Int) (820140334435874266915193800869516911316263523032777500425290296414193700538685303063129806311707886781771 : Int)
    geometryRow033_jensenBound_numerator_no_slash geometryRow033_jensenBound_numerator_parse
    geometryRow033_jensenBound_denominator_parse geometryRow033_jensenBound_denominator_nonzero

theorem geometryRow033_jensenBound_read :
    rationalField geometryRowsJson033 "jensen_bound" = .ok geometryRowsTyped033.jensenBound :=
  original_rationalField_of_string geometryRowsJson033 "jensen_bound" geometryRow033_jensenBoundText
    geometryRowsTyped033.jensenBound geometryRow033_jensenBound_field geometryRow033_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_factorMaxima_before"
  err.flush

theorem geometryRow033_factorMaxima_read :
    rationalArrayField geometryRowsJson033 "factor_maxima" = .ok geometryRowsTyped033.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_gapWeightedMeans_before"
  err.flush

theorem geometryRow033_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson033 "gap_weighted_means" = .ok geometryRowsTyped033.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow033_floorChars : List Char := ['2', '5', '4', '8', '8', '2', '7', '3', '8', '5', '4', '8', '6', '6', '2', '6', '1', '7', '9', '8']
noncomputable def geometryRow033_floorText : String := String.ofList geometryRow033_floorChars

theorem geometryRow033_floor_text_read :
    geometryRowsJson033.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow033_floorText := by rfl

theorem geometryRow033_floor_chars_parse :
    SourceJson.intChars geometryRow033_floorChars = some (25488273854866261798 : Int) := by decide +kernel

theorem geometryRow033_floor_parse :
    parseInteger geometryRow033_floorText = .ok geometryRowsTyped033.jensenFloorQ96 := by
  simp only [geometryRow033_floorText, parseInteger, String.toList_ofList, geometryRow033_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_033 :
    decodeGeometryRow geometryRowsJson033 = .ok geometryRowsTyped033 :=
  original_geometryRow_of_fields geometryRowsJson033 geometryRowsTyped033 geometryRow033_floorText
    geometryRow033_simplexId_read geometryRow033_vertexIds_read
    geometryRow033_physicalVolume_read geometryRow033_meanGap_read
    geometryRow033_factorMaxima_read geometryRow033_gapWeightedMeans_read
    geometryRow033_jensenBound_read geometryRow033_floor_text_read geometryRow033_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_033_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock016 : List SourceJson := [geometryRowsJson032, geometryRowsJson033]
noncomputable def geometryRowsTypedBlock016 : List (GeometryRow) := [geometryRowsTyped032, geometryRowsTyped033]
noncomputable def geometryRowsTypedThroughBlock016 : List (GeometryRow) := geometryRowsTypedThroughBlock015 ++ geometryRowsTypedBlock016

theorem geometry_Rows_block_016_push_eq (acc : List SourceJson) :
    SimplicesBlock016.blockPush acc = [geometryRowsJson033, geometryRowsJson032] ++ acc := by rfl

theorem geometry_Rows_block_016_reverse (acc : List SourceJson) :
    (SimplicesBlock016.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock016 := by
  rw [geometry_Rows_block_016_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_016 :
    geometryRowsJsonBlock016.mapM decodeGeometryRow = .ok geometryRowsTypedBlock016 := by
  simp only [geometryRowsJsonBlock016, geometryRowsTypedBlock016, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_032, decode_geometry_Rows_033]
  rfl

theorem decode_geometry_Rows_through_block_016 :
    SimplicesValue.arrayAcc017.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock016 := by
  change (SimplicesBlock016.blockPush SimplicesValue.arrayAcc016).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_016_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_015, decode_geometry_Rows_block_016]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_016_complete"
  err.flush

#print axioms geometryRow032_simplexId_read
#print axioms geometryRow032_vertexIds_read
#print axioms geometryRow032_physicalVolume_field
#print axioms geometryRow032_physicalVolume_numerator_no_slash
#print axioms geometryRow032_physicalVolume_numerator_parse
#print axioms geometryRow032_physicalVolume_denominator_parse
#print axioms geometryRow032_physicalVolume_denominator_nonzero
#print axioms geometryRow032_physicalVolume_parse
#print axioms geometryRow032_physicalVolume_read
#print axioms geometryRow032_meanGap_field
#print axioms geometryRow032_meanGap_numerator_no_slash
#print axioms geometryRow032_meanGap_numerator_parse
#print axioms geometryRow032_meanGap_denominator_parse
#print axioms geometryRow032_meanGap_denominator_nonzero
#print axioms geometryRow032_meanGap_parse
#print axioms geometryRow032_meanGap_read
#print axioms geometryRow032_jensenBound_field
#print axioms geometryRow032_jensenBound_numerator_no_slash
#print axioms geometryRow032_jensenBound_numerator_parse
#print axioms geometryRow032_jensenBound_denominator_parse
#print axioms geometryRow032_jensenBound_denominator_nonzero
#print axioms geometryRow032_jensenBound_parse
#print axioms geometryRow032_jensenBound_read
#print axioms geometryRow032_factorMaxima_read
#print axioms geometryRow032_gapWeightedMeans_read
#print axioms geometryRow032_floor_text_read
#print axioms geometryRow032_floor_chars_parse
#print axioms geometryRow032_floor_parse
#print axioms decode_geometry_Rows_032
#print axioms geometryRow033_simplexId_read
#print axioms geometryRow033_vertexIds_read
#print axioms geometryRow033_physicalVolume_field
#print axioms geometryRow033_physicalVolume_numerator_no_slash
#print axioms geometryRow033_physicalVolume_numerator_parse
#print axioms geometryRow033_physicalVolume_denominator_parse
#print axioms geometryRow033_physicalVolume_denominator_nonzero
#print axioms geometryRow033_physicalVolume_parse
#print axioms geometryRow033_physicalVolume_read
#print axioms geometryRow033_meanGap_field
#print axioms geometryRow033_meanGap_numerator_no_slash
#print axioms geometryRow033_meanGap_numerator_parse
#print axioms geometryRow033_meanGap_denominator_parse
#print axioms geometryRow033_meanGap_denominator_nonzero
#print axioms geometryRow033_meanGap_parse
#print axioms geometryRow033_meanGap_read
#print axioms geometryRow033_jensenBound_field
#print axioms geometryRow033_jensenBound_numerator_no_slash
#print axioms geometryRow033_jensenBound_numerator_parse
#print axioms geometryRow033_jensenBound_denominator_parse
#print axioms geometryRow033_jensenBound_denominator_nonzero
#print axioms geometryRow033_jensenBound_parse
#print axioms geometryRow033_jensenBound_read
#print axioms geometryRow033_factorMaxima_read
#print axioms geometryRow033_gapWeightedMeans_read
#print axioms geometryRow033_floor_text_read
#print axioms geometryRow033_floor_chars_parse
#print axioms geometryRow033_floor_parse
#print axioms decode_geometry_Rows_033
#print axioms geometry_Rows_block_016_push_eq
#print axioms geometry_Rows_block_016_reverse
#print axioms decode_geometry_Rows_block_016
#print axioms decode_geometry_Rows_through_block_016

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
