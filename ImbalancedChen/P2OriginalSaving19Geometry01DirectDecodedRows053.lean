import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows052

/-! Original simplices typed block 53, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson104 : SourceJson :=
  (SimplicesBlock053.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped104 : GeometryRow :=
  { simplexId := 104,
    vertexIds := #[39, 37, 24, 22, 19, 18, 7, 6, 0],
    physicalVolume := ((211728042938180003531624864600979901515691 : ℚ) / (1218175352159109120000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((807 : ℚ) / (17792 : ℚ))],
    gapWeightedMeans := #[((2324318117 : ℚ) / (28885937500 : ℚ)), ((149161224123 : ℚ) / (1848700000000 : ℚ)), ((2427768895807 : ℚ) / (16638300000000 : ℚ)), ((300680049113 : ℚ) / (2773050000000 : ℚ)), ((1757680491559 : ℚ) / (33276600000000 : ℚ)), ((798680747321 : ℚ) / (16638300000000 : ℚ)), ((278497216217 : ℚ) / (6655320000000 : ℚ)), ((271389206021 : ℚ) / (6655320000000 : ℚ)), ((271388762333 : ℚ) / (6655320000000 : ℚ)), ((631009441159 : ℚ) / (16638300000000 : ℚ))],
    jensenBound := ((2168413930398082529664719045139856616856174466783281736749704912808621279307549438476562500000000 : ℚ) / (17618837459457732506615961412240306977570894008847735694500218760572174798643091130443507217855410440962109249101 : ℚ)),
    jensenFloorQ96 := (9750895975463 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_simplexId_before"
  err.flush

theorem geometryRow104_simplexId_read :
    geometryRowsJson104.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped104.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_vertexIds_before"
  err.flush

theorem geometryRow104_vertexIds_read :
    geometryRowsJson104.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped104.vertexIds := by decide +kernel

noncomputable def geometryRow104_physicalVolumeNumeratorChars : List Char := ['2', '1', '1', '7', '2', '8', '0', '4', '2', '9', '3', '8', '1', '8', '0', '0', '0', '3', '5', '3', '1', '6', '2', '4', '8', '6', '4', '6', '0', '0', '9', '7', '9', '9', '0', '1', '5', '1', '5', '6', '9', '1']
noncomputable def geometryRow104_physicalVolumeDenominatorChars : List Char := ['1', '2', '1', '8', '1', '7', '5', '3', '5', '2', '1', '5', '9', '1', '0', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow104_physicalVolumeText : String := String.ofList (geometryRow104_physicalVolumeNumeratorChars ++ '/' :: geometryRow104_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_physicalVolume_before_field"
  err.flush

theorem geometryRow104_physicalVolume_field :
    geometryRowsJson104.getObjVal? "physical_volume" = .ok (.str geometryRow104_physicalVolumeText) := by rfl

theorem geometryRow104_physicalVolume_numerator_no_slash :
    geometryRow104_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow104_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow104_physicalVolumeNumeratorChars = some (211728042938180003531624864600979901515691 : Int) := by decide +kernel

theorem geometryRow104_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow104_physicalVolumeDenominatorChars = some (1218175352159109120000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow104_physicalVolume_denominator_nonzero : (1218175352159109120000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow104_physicalVolume_parse :
    parseRational geometryRow104_physicalVolumeText = .ok geometryRowsTyped104.physicalVolume :=
  original_rational_fraction_of_chars geometryRow104_physicalVolumeNumeratorChars geometryRow104_physicalVolumeDenominatorChars
    (211728042938180003531624864600979901515691 : Int) (1218175352159109120000000000000000000000000000000000000000000000000 : Int)
    geometryRow104_physicalVolume_numerator_no_slash geometryRow104_physicalVolume_numerator_parse
    geometryRow104_physicalVolume_denominator_parse geometryRow104_physicalVolume_denominator_nonzero

theorem geometryRow104_physicalVolume_read :
    rationalField geometryRowsJson104 "physical_volume" = .ok geometryRowsTyped104.physicalVolume :=
  original_rationalField_of_string geometryRowsJson104 "physical_volume" geometryRow104_physicalVolumeText
    geometryRowsTyped104.physicalVolume geometryRow104_physicalVolume_field geometryRow104_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_physicalVolume_complete"
  err.flush

noncomputable def geometryRow104_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow104_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow104_meanGapText : String := String.ofList (geometryRow104_meanGapNumeratorChars ++ '/' :: geometryRow104_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_meanGap_before_field"
  err.flush

theorem geometryRow104_meanGap_field :
    geometryRowsJson104.getObjVal? "mean_gap" = .ok (.str geometryRow104_meanGapText) := by rfl

theorem geometryRow104_meanGap_numerator_no_slash :
    geometryRow104_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow104_meanGap_numerator_parse :
    SourceJson.intChars geometryRow104_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow104_meanGap_denominator_parse :
    SourceJson.intChars geometryRow104_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow104_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow104_meanGap_parse :
    parseRational geometryRow104_meanGapText = .ok geometryRowsTyped104.meanGap :=
  original_rational_fraction_of_chars geometryRow104_meanGapNumeratorChars geometryRow104_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow104_meanGap_numerator_no_slash geometryRow104_meanGap_numerator_parse
    geometryRow104_meanGap_denominator_parse geometryRow104_meanGap_denominator_nonzero

theorem geometryRow104_meanGap_read :
    rationalField geometryRowsJson104 "mean_gap" = .ok geometryRowsTyped104.meanGap :=
  original_rationalField_of_string geometryRowsJson104 "mean_gap" geometryRow104_meanGapText
    geometryRowsTyped104.meanGap geometryRow104_meanGap_field geometryRow104_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_meanGap_complete"
  err.flush

noncomputable def geometryRow104_jensenBoundNumeratorChars : List Char := ['2', '1', '6', '8', '4', '1', '3', '9', '3', '0', '3', '9', '8', '0', '8', '2', '5', '2', '9', '6', '6', '4', '7', '1', '9', '0', '4', '5', '1', '3', '9', '8', '5', '6', '6', '1', '6', '8', '5', '6', '1', '7', '4', '4', '6', '6', '7', '8', '3', '2', '8', '1', '7', '3', '6', '7', '4', '9', '7', '0', '4', '9', '1', '2', '8', '0', '8', '6', '2', '1', '2', '7', '9', '3', '0', '7', '5', '4', '9', '4', '3', '8', '4', '7', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow104_jensenBoundDenominatorChars : List Char := ['1', '7', '6', '1', '8', '8', '3', '7', '4', '5', '9', '4', '5', '7', '7', '3', '2', '5', '0', '6', '6', '1', '5', '9', '6', '1', '4', '1', '2', '2', '4', '0', '3', '0', '6', '9', '7', '7', '5', '7', '0', '8', '9', '4', '0', '0', '8', '8', '4', '7', '7', '3', '5', '6', '9', '4', '5', '0', '0', '2', '1', '8', '7', '6', '0', '5', '7', '2', '1', '7', '4', '7', '9', '8', '6', '4', '3', '0', '9', '1', '1', '3', '0', '4', '4', '3', '5', '0', '7', '2', '1', '7', '8', '5', '5', '4', '1', '0', '4', '4', '0', '9', '6', '2', '1', '0', '9', '2', '4', '9', '1', '0', '1']
noncomputable def geometryRow104_jensenBoundText : String := String.ofList (geometryRow104_jensenBoundNumeratorChars ++ '/' :: geometryRow104_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_jensenBound_before_field"
  err.flush

theorem geometryRow104_jensenBound_field :
    geometryRowsJson104.getObjVal? "jensen_bound" = .ok (.str geometryRow104_jensenBoundText) := by rfl

theorem geometryRow104_jensenBound_numerator_no_slash :
    geometryRow104_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow104_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow104_jensenBoundNumeratorChars = some (2168413930398082529664719045139856616856174466783281736749704912808621279307549438476562500000000 : Int) := by decide +kernel

theorem geometryRow104_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow104_jensenBoundDenominatorChars = some (17618837459457732506615961412240306977570894008847735694500218760572174798643091130443507217855410440962109249101 : Int) := by decide +kernel

theorem geometryRow104_jensenBound_denominator_nonzero : (17618837459457732506615961412240306977570894008847735694500218760572174798643091130443507217855410440962109249101 : Int) ≠ 0 := by decide +kernel

theorem geometryRow104_jensenBound_parse :
    parseRational geometryRow104_jensenBoundText = .ok geometryRowsTyped104.jensenBound :=
  original_rational_fraction_of_chars geometryRow104_jensenBoundNumeratorChars geometryRow104_jensenBoundDenominatorChars
    (2168413930398082529664719045139856616856174466783281736749704912808621279307549438476562500000000 : Int) (17618837459457732506615961412240306977570894008847735694500218760572174798643091130443507217855410440962109249101 : Int)
    geometryRow104_jensenBound_numerator_no_slash geometryRow104_jensenBound_numerator_parse
    geometryRow104_jensenBound_denominator_parse geometryRow104_jensenBound_denominator_nonzero

theorem geometryRow104_jensenBound_read :
    rationalField geometryRowsJson104 "jensen_bound" = .ok geometryRowsTyped104.jensenBound :=
  original_rationalField_of_string geometryRowsJson104 "jensen_bound" geometryRow104_jensenBoundText
    geometryRowsTyped104.jensenBound geometryRow104_jensenBound_field geometryRow104_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_factorMaxima_before"
  err.flush

theorem geometryRow104_factorMaxima_read :
    rationalArrayField geometryRowsJson104 "factor_maxima" = .ok geometryRowsTyped104.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_gapWeightedMeans_before"
  err.flush

theorem geometryRow104_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson104 "gap_weighted_means" = .ok geometryRowsTyped104.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow104_floorChars : List Char := ['9', '7', '5', '0', '8', '9', '5', '9', '7', '5', '4', '6', '3']
noncomputable def geometryRow104_floorText : String := String.ofList geometryRow104_floorChars

theorem geometryRow104_floor_text_read :
    geometryRowsJson104.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow104_floorText := by rfl

theorem geometryRow104_floor_chars_parse :
    SourceJson.intChars geometryRow104_floorChars = some (9750895975463 : Int) := by decide +kernel

theorem geometryRow104_floor_parse :
    parseInteger geometryRow104_floorText = .ok geometryRowsTyped104.jensenFloorQ96 := by
  simp only [geometryRow104_floorText, parseInteger, String.toList_ofList, geometryRow104_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_104 :
    decodeGeometryRow geometryRowsJson104 = .ok geometryRowsTyped104 :=
  original_geometryRow_of_fields geometryRowsJson104 geometryRowsTyped104 geometryRow104_floorText
    geometryRow104_simplexId_read geometryRow104_vertexIds_read
    geometryRow104_physicalVolume_read geometryRow104_meanGap_read
    geometryRow104_factorMaxima_read geometryRow104_gapWeightedMeans_read
    geometryRow104_jensenBound_read geometryRow104_floor_text_read geometryRow104_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_104_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson105 : SourceJson :=
  (SimplicesBlock053.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped105 : GeometryRow :=
  { simplexId := 105,
    vertexIds := #[39, 37, 24, 22, 19, 18, 15, 7, 0],
    physicalVolume := ((74024604455942242113756805546071531885871 : ℚ) / (1252980362220797952000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((65244130397 : ℚ) / (831915000000 : ℚ)), ((261705277931 : ℚ) / (3327660000000 : ℚ)), ((1461812435791 : ℚ) / (9982980000000 : ℚ)), ((47618659703 : ℚ) / (443688000000 : ℚ)), ((1039404616771 : ℚ) / (19965960000000 : ℚ)), ((120352393103 : ℚ) / (2495745000000 : ℚ)), ((21206114651 : ℚ) / (499149000000 : ℚ)), ((206730138863 : ℚ) / (4991490000000 : ℚ)), ((206729806097 : ℚ) / (4991490000000 : ℚ)), ((789570192983 : ℚ) / (19965960000000 : ℚ))],
    jensenBound := ((4362040799357886517249107441798314665388722920258342384266194937085607026342821099537988281250000 : ℚ) / (106394912902222720784874835788379003376906972965834082678345322444090203907128639721563985582659824546743155147809 : ℚ)),
    jensenFloorQ96 := (3248242495042 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_simplexId_before"
  err.flush

theorem geometryRow105_simplexId_read :
    geometryRowsJson105.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped105.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_vertexIds_before"
  err.flush

theorem geometryRow105_vertexIds_read :
    geometryRowsJson105.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped105.vertexIds := by decide +kernel

noncomputable def geometryRow105_physicalVolumeNumeratorChars : List Char := ['7', '4', '0', '2', '4', '6', '0', '4', '4', '5', '5', '9', '4', '2', '2', '4', '2', '1', '1', '3', '7', '5', '6', '8', '0', '5', '5', '4', '6', '0', '7', '1', '5', '3', '1', '8', '8', '5', '8', '7', '1']
noncomputable def geometryRow105_physicalVolumeDenominatorChars : List Char := ['1', '2', '5', '2', '9', '8', '0', '3', '6', '2', '2', '2', '0', '7', '9', '7', '9', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow105_physicalVolumeText : String := String.ofList (geometryRow105_physicalVolumeNumeratorChars ++ '/' :: geometryRow105_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_physicalVolume_before_field"
  err.flush

theorem geometryRow105_physicalVolume_field :
    geometryRowsJson105.getObjVal? "physical_volume" = .ok (.str geometryRow105_physicalVolumeText) := by rfl

theorem geometryRow105_physicalVolume_numerator_no_slash :
    geometryRow105_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow105_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow105_physicalVolumeNumeratorChars = some (74024604455942242113756805546071531885871 : Int) := by decide +kernel

theorem geometryRow105_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow105_physicalVolumeDenominatorChars = some (1252980362220797952000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow105_physicalVolume_denominator_nonzero : (1252980362220797952000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow105_physicalVolume_parse :
    parseRational geometryRow105_physicalVolumeText = .ok geometryRowsTyped105.physicalVolume :=
  original_rational_fraction_of_chars geometryRow105_physicalVolumeNumeratorChars geometryRow105_physicalVolumeDenominatorChars
    (74024604455942242113756805546071531885871 : Int) (1252980362220797952000000000000000000000000000000000000000000000000 : Int)
    geometryRow105_physicalVolume_numerator_no_slash geometryRow105_physicalVolume_numerator_parse
    geometryRow105_physicalVolume_denominator_parse geometryRow105_physicalVolume_denominator_nonzero

theorem geometryRow105_physicalVolume_read :
    rationalField geometryRowsJson105 "physical_volume" = .ok geometryRowsTyped105.physicalVolume :=
  original_rationalField_of_string geometryRowsJson105 "physical_volume" geometryRow105_physicalVolumeText
    geometryRowsTyped105.physicalVolume geometryRow105_physicalVolume_field geometryRow105_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_physicalVolume_complete"
  err.flush

noncomputable def geometryRow105_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow105_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow105_meanGapText : String := String.ofList (geometryRow105_meanGapNumeratorChars ++ '/' :: geometryRow105_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_meanGap_before_field"
  err.flush

theorem geometryRow105_meanGap_field :
    geometryRowsJson105.getObjVal? "mean_gap" = .ok (.str geometryRow105_meanGapText) := by rfl

theorem geometryRow105_meanGap_numerator_no_slash :
    geometryRow105_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow105_meanGap_numerator_parse :
    SourceJson.intChars geometryRow105_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow105_meanGap_denominator_parse :
    SourceJson.intChars geometryRow105_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow105_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow105_meanGap_parse :
    parseRational geometryRow105_meanGapText = .ok geometryRowsTyped105.meanGap :=
  original_rational_fraction_of_chars geometryRow105_meanGapNumeratorChars geometryRow105_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow105_meanGap_numerator_no_slash geometryRow105_meanGap_numerator_parse
    geometryRow105_meanGap_denominator_parse geometryRow105_meanGap_denominator_nonzero

theorem geometryRow105_meanGap_read :
    rationalField geometryRowsJson105 "mean_gap" = .ok geometryRowsTyped105.meanGap :=
  original_rationalField_of_string geometryRowsJson105 "mean_gap" geometryRow105_meanGapText
    geometryRowsTyped105.meanGap geometryRow105_meanGap_field geometryRow105_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_meanGap_complete"
  err.flush

noncomputable def geometryRow105_jensenBoundNumeratorChars : List Char := ['4', '3', '6', '2', '0', '4', '0', '7', '9', '9', '3', '5', '7', '8', '8', '6', '5', '1', '7', '2', '4', '9', '1', '0', '7', '4', '4', '1', '7', '9', '8', '3', '1', '4', '6', '6', '5', '3', '8', '8', '7', '2', '2', '9', '2', '0', '2', '5', '8', '3', '4', '2', '3', '8', '4', '2', '6', '6', '1', '9', '4', '9', '3', '7', '0', '8', '5', '6', '0', '7', '0', '2', '6', '3', '4', '2', '8', '2', '1', '0', '9', '9', '5', '3', '7', '9', '8', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0']
noncomputable def geometryRow105_jensenBoundDenominatorChars : List Char := ['1', '0', '6', '3', '9', '4', '9', '1', '2', '9', '0', '2', '2', '2', '2', '7', '2', '0', '7', '8', '4', '8', '7', '4', '8', '3', '5', '7', '8', '8', '3', '7', '9', '0', '0', '3', '3', '7', '6', '9', '0', '6', '9', '7', '2', '9', '6', '5', '8', '3', '4', '0', '8', '2', '6', '7', '8', '3', '4', '5', '3', '2', '2', '4', '4', '4', '0', '9', '0', '2', '0', '3', '9', '0', '7', '1', '2', '8', '6', '3', '9', '7', '2', '1', '5', '6', '3', '9', '8', '5', '5', '8', '2', '6', '5', '9', '8', '2', '4', '5', '4', '6', '7', '4', '3', '1', '5', '5', '1', '4', '7', '8', '0', '9']
noncomputable def geometryRow105_jensenBoundText : String := String.ofList (geometryRow105_jensenBoundNumeratorChars ++ '/' :: geometryRow105_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_jensenBound_before_field"
  err.flush

theorem geometryRow105_jensenBound_field :
    geometryRowsJson105.getObjVal? "jensen_bound" = .ok (.str geometryRow105_jensenBoundText) := by rfl

theorem geometryRow105_jensenBound_numerator_no_slash :
    geometryRow105_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow105_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow105_jensenBoundNumeratorChars = some (4362040799357886517249107441798314665388722920258342384266194937085607026342821099537988281250000 : Int) := by decide +kernel

theorem geometryRow105_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow105_jensenBoundDenominatorChars = some (106394912902222720784874835788379003376906972965834082678345322444090203907128639721563985582659824546743155147809 : Int) := by decide +kernel

theorem geometryRow105_jensenBound_denominator_nonzero : (106394912902222720784874835788379003376906972965834082678345322444090203907128639721563985582659824546743155147809 : Int) ≠ 0 := by decide +kernel

theorem geometryRow105_jensenBound_parse :
    parseRational geometryRow105_jensenBoundText = .ok geometryRowsTyped105.jensenBound :=
  original_rational_fraction_of_chars geometryRow105_jensenBoundNumeratorChars geometryRow105_jensenBoundDenominatorChars
    (4362040799357886517249107441798314665388722920258342384266194937085607026342821099537988281250000 : Int) (106394912902222720784874835788379003376906972965834082678345322444090203907128639721563985582659824546743155147809 : Int)
    geometryRow105_jensenBound_numerator_no_slash geometryRow105_jensenBound_numerator_parse
    geometryRow105_jensenBound_denominator_parse geometryRow105_jensenBound_denominator_nonzero

theorem geometryRow105_jensenBound_read :
    rationalField geometryRowsJson105 "jensen_bound" = .ok geometryRowsTyped105.jensenBound :=
  original_rationalField_of_string geometryRowsJson105 "jensen_bound" geometryRow105_jensenBoundText
    geometryRowsTyped105.jensenBound geometryRow105_jensenBound_field geometryRow105_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_factorMaxima_before"
  err.flush

theorem geometryRow105_factorMaxima_read :
    rationalArrayField geometryRowsJson105 "factor_maxima" = .ok geometryRowsTyped105.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_gapWeightedMeans_before"
  err.flush

theorem geometryRow105_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson105 "gap_weighted_means" = .ok geometryRowsTyped105.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow105_floorChars : List Char := ['3', '2', '4', '8', '2', '4', '2', '4', '9', '5', '0', '4', '2']
noncomputable def geometryRow105_floorText : String := String.ofList geometryRow105_floorChars

theorem geometryRow105_floor_text_read :
    geometryRowsJson105.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow105_floorText := by rfl

theorem geometryRow105_floor_chars_parse :
    SourceJson.intChars geometryRow105_floorChars = some (3248242495042 : Int) := by decide +kernel

theorem geometryRow105_floor_parse :
    parseInteger geometryRow105_floorText = .ok geometryRowsTyped105.jensenFloorQ96 := by
  simp only [geometryRow105_floorText, parseInteger, String.toList_ofList, geometryRow105_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_105 :
    decodeGeometryRow geometryRowsJson105 = .ok geometryRowsTyped105 :=
  original_geometryRow_of_fields geometryRowsJson105 geometryRowsTyped105 geometryRow105_floorText
    geometryRow105_simplexId_read geometryRow105_vertexIds_read
    geometryRow105_physicalVolume_read geometryRow105_meanGap_read
    geometryRow105_factorMaxima_read geometryRow105_gapWeightedMeans_read
    geometryRow105_jensenBound_read geometryRow105_floor_text_read geometryRow105_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_105_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock053 : List SourceJson := [geometryRowsJson104, geometryRowsJson105]
noncomputable def geometryRowsTypedBlock053 : List (GeometryRow) := [geometryRowsTyped104, geometryRowsTyped105]
noncomputable def geometryRowsTypedThroughBlock053 : List (GeometryRow) := geometryRowsTypedThroughBlock052 ++ geometryRowsTypedBlock053

theorem geometry_Rows_block_053_push_eq (acc : List SourceJson) :
    SimplicesBlock053.blockPush acc = [geometryRowsJson105, geometryRowsJson104] ++ acc := by rfl

theorem geometry_Rows_block_053_reverse (acc : List SourceJson) :
    (SimplicesBlock053.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock053 := by
  rw [geometry_Rows_block_053_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_053 :
    geometryRowsJsonBlock053.mapM decodeGeometryRow = .ok geometryRowsTypedBlock053 := by
  simp only [geometryRowsJsonBlock053, geometryRowsTypedBlock053, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_104, decode_geometry_Rows_105]
  rfl

theorem decode_geometry_Rows_through_block_053 :
    SimplicesValue.arrayAcc054.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock053 := by
  change (SimplicesBlock053.blockPush SimplicesValue.arrayAcc053).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_053_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_052, decode_geometry_Rows_block_053]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_053_complete"
  err.flush

#print axioms geometryRow104_simplexId_read
#print axioms geometryRow104_vertexIds_read
#print axioms geometryRow104_physicalVolume_field
#print axioms geometryRow104_physicalVolume_numerator_no_slash
#print axioms geometryRow104_physicalVolume_numerator_parse
#print axioms geometryRow104_physicalVolume_denominator_parse
#print axioms geometryRow104_physicalVolume_denominator_nonzero
#print axioms geometryRow104_physicalVolume_parse
#print axioms geometryRow104_physicalVolume_read
#print axioms geometryRow104_meanGap_field
#print axioms geometryRow104_meanGap_numerator_no_slash
#print axioms geometryRow104_meanGap_numerator_parse
#print axioms geometryRow104_meanGap_denominator_parse
#print axioms geometryRow104_meanGap_denominator_nonzero
#print axioms geometryRow104_meanGap_parse
#print axioms geometryRow104_meanGap_read
#print axioms geometryRow104_jensenBound_field
#print axioms geometryRow104_jensenBound_numerator_no_slash
#print axioms geometryRow104_jensenBound_numerator_parse
#print axioms geometryRow104_jensenBound_denominator_parse
#print axioms geometryRow104_jensenBound_denominator_nonzero
#print axioms geometryRow104_jensenBound_parse
#print axioms geometryRow104_jensenBound_read
#print axioms geometryRow104_factorMaxima_read
#print axioms geometryRow104_gapWeightedMeans_read
#print axioms geometryRow104_floor_text_read
#print axioms geometryRow104_floor_chars_parse
#print axioms geometryRow104_floor_parse
#print axioms decode_geometry_Rows_104
#print axioms geometryRow105_simplexId_read
#print axioms geometryRow105_vertexIds_read
#print axioms geometryRow105_physicalVolume_field
#print axioms geometryRow105_physicalVolume_numerator_no_slash
#print axioms geometryRow105_physicalVolume_numerator_parse
#print axioms geometryRow105_physicalVolume_denominator_parse
#print axioms geometryRow105_physicalVolume_denominator_nonzero
#print axioms geometryRow105_physicalVolume_parse
#print axioms geometryRow105_physicalVolume_read
#print axioms geometryRow105_meanGap_field
#print axioms geometryRow105_meanGap_numerator_no_slash
#print axioms geometryRow105_meanGap_numerator_parse
#print axioms geometryRow105_meanGap_denominator_parse
#print axioms geometryRow105_meanGap_denominator_nonzero
#print axioms geometryRow105_meanGap_parse
#print axioms geometryRow105_meanGap_read
#print axioms geometryRow105_jensenBound_field
#print axioms geometryRow105_jensenBound_numerator_no_slash
#print axioms geometryRow105_jensenBound_numerator_parse
#print axioms geometryRow105_jensenBound_denominator_parse
#print axioms geometryRow105_jensenBound_denominator_nonzero
#print axioms geometryRow105_jensenBound_parse
#print axioms geometryRow105_jensenBound_read
#print axioms geometryRow105_factorMaxima_read
#print axioms geometryRow105_gapWeightedMeans_read
#print axioms geometryRow105_floor_text_read
#print axioms geometryRow105_floor_chars_parse
#print axioms geometryRow105_floor_parse
#print axioms decode_geometry_Rows_105
#print axioms geometry_Rows_block_053_push_eq
#print axioms geometry_Rows_block_053_reverse
#print axioms decode_geometry_Rows_block_053
#print axioms decode_geometry_Rows_through_block_053

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
