import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows064

/-! Original simplices typed block 65, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson128 : SourceJson :=
  (SimplicesBlock065.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped128 : GeometryRow :=
  { simplexId := 128,
    vertexIds := #[39, 38, 34, 24, 23, 21, 20, 16, 1],
    physicalVolume := ((1592197522079163954791502511978838850123551 : ℚ) / (262211192980144128000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((7711581814279 : ℚ) / (104802480000000 : ℚ)), ((7731151041283 : ℚ) / (104802480000000 : ℚ)), ((46778383169147 : ℚ) / (314407440000000 : ℚ)), ((98798195857 : ℚ) / (909743750000 : ℚ)), ((88848466399349 : ℚ) / (1572037200000000 : ℚ)), ((72352775660597 : ℚ) / (1572037200000000 : ℚ)), ((3446641622467 : ℚ) / (82738800000000 : ℚ)), ((64646773984333 : ℚ) / (1572037200000000 : ℚ)), ((63758959091839 : ℚ) / (1572037200000000 : ℚ)), ((63758854289359 : ℚ) / (1572037200000000 : ℚ))],
    jensenBound := ((28010253285786309839431954807887126064390623481669362134750567908581037029743122799881381076278800000000000000000000 : ℚ) / (7146856884517301257881666263294836553700925647271287366801458150360983202333775736319604905153570025158223399100000629982708179940891 : ℚ)),
    jensenFloorQ96 := (310514249165 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_simplexId_before"
  err.flush

theorem geometryRow128_simplexId_read :
    geometryRowsJson128.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped128.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_vertexIds_before"
  err.flush

theorem geometryRow128_vertexIds_read :
    geometryRowsJson128.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped128.vertexIds := by decide +kernel

noncomputable def geometryRow128_physicalVolumeNumeratorChars : List Char := ['1', '5', '9', '2', '1', '9', '7', '5', '2', '2', '0', '7', '9', '1', '6', '3', '9', '5', '4', '7', '9', '1', '5', '0', '2', '5', '1', '1', '9', '7', '8', '8', '3', '8', '8', '5', '0', '1', '2', '3', '5', '5', '1']
noncomputable def geometryRow128_physicalVolumeDenominatorChars : List Char := ['2', '6', '2', '2', '1', '1', '1', '9', '2', '9', '8', '0', '1', '4', '4', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow128_physicalVolumeText : String := String.ofList (geometryRow128_physicalVolumeNumeratorChars ++ '/' :: geometryRow128_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_physicalVolume_before_field"
  err.flush

theorem geometryRow128_physicalVolume_field :
    geometryRowsJson128.getObjVal? "physical_volume" = .ok (.str geometryRow128_physicalVolumeText) := by rfl

theorem geometryRow128_physicalVolume_numerator_no_slash :
    geometryRow128_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow128_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow128_physicalVolumeNumeratorChars = some (1592197522079163954791502511978838850123551 : Int) := by decide +kernel

theorem geometryRow128_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow128_physicalVolumeDenominatorChars = some (262211192980144128000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow128_physicalVolume_denominator_nonzero : (262211192980144128000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow128_physicalVolume_parse :
    parseRational geometryRow128_physicalVolumeText = .ok geometryRowsTyped128.physicalVolume :=
  original_rational_fraction_of_chars geometryRow128_physicalVolumeNumeratorChars geometryRow128_physicalVolumeDenominatorChars
    (1592197522079163954791502511978838850123551 : Int) (262211192980144128000000000000000000000000000000000000000000000000000 : Int)
    geometryRow128_physicalVolume_numerator_no_slash geometryRow128_physicalVolume_numerator_parse
    geometryRow128_physicalVolume_denominator_parse geometryRow128_physicalVolume_denominator_nonzero

theorem geometryRow128_physicalVolume_read :
    rationalField geometryRowsJson128 "physical_volume" = .ok geometryRowsTyped128.physicalVolume :=
  original_rationalField_of_string geometryRowsJson128 "physical_volume" geometryRow128_physicalVolumeText
    geometryRowsTyped128.physicalVolume geometryRow128_physicalVolume_field geometryRow128_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_physicalVolume_complete"
  err.flush

noncomputable def geometryRow128_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow128_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow128_meanGapText : String := String.ofList (geometryRow128_meanGapNumeratorChars ++ '/' :: geometryRow128_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_meanGap_before_field"
  err.flush

theorem geometryRow128_meanGap_field :
    geometryRowsJson128.getObjVal? "mean_gap" = .ok (.str geometryRow128_meanGapText) := by rfl

theorem geometryRow128_meanGap_numerator_no_slash :
    geometryRow128_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow128_meanGap_numerator_parse :
    SourceJson.intChars geometryRow128_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow128_meanGap_denominator_parse :
    SourceJson.intChars geometryRow128_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow128_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow128_meanGap_parse :
    parseRational geometryRow128_meanGapText = .ok geometryRowsTyped128.meanGap :=
  original_rational_fraction_of_chars geometryRow128_meanGapNumeratorChars geometryRow128_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow128_meanGap_numerator_no_slash geometryRow128_meanGap_numerator_parse
    geometryRow128_meanGap_denominator_parse geometryRow128_meanGap_denominator_nonzero

theorem geometryRow128_meanGap_read :
    rationalField geometryRowsJson128 "mean_gap" = .ok geometryRowsTyped128.meanGap :=
  original_rationalField_of_string geometryRowsJson128 "mean_gap" geometryRow128_meanGapText
    geometryRowsTyped128.meanGap geometryRow128_meanGap_field geometryRow128_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_meanGap_complete"
  err.flush

noncomputable def geometryRow128_jensenBoundNumeratorChars : List Char := ['2', '8', '0', '1', '0', '2', '5', '3', '2', '8', '5', '7', '8', '6', '3', '0', '9', '8', '3', '9', '4', '3', '1', '9', '5', '4', '8', '0', '7', '8', '8', '7', '1', '2', '6', '0', '6', '4', '3', '9', '0', '6', '2', '3', '4', '8', '1', '6', '6', '9', '3', '6', '2', '1', '3', '4', '7', '5', '0', '5', '6', '7', '9', '0', '8', '5', '8', '1', '0', '3', '7', '0', '2', '9', '7', '4', '3', '1', '2', '2', '7', '9', '9', '8', '8', '1', '3', '8', '1', '0', '7', '6', '2', '7', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow128_jensenBoundDenominatorChars : List Char := ['7', '1', '4', '6', '8', '5', '6', '8', '8', '4', '5', '1', '7', '3', '0', '1', '2', '5', '7', '8', '8', '1', '6', '6', '6', '2', '6', '3', '2', '9', '4', '8', '3', '6', '5', '5', '3', '7', '0', '0', '9', '2', '5', '6', '4', '7', '2', '7', '1', '2', '8', '7', '3', '6', '6', '8', '0', '1', '4', '5', '8', '1', '5', '0', '3', '6', '0', '9', '8', '3', '2', '0', '2', '3', '3', '3', '7', '7', '5', '7', '3', '6', '3', '1', '9', '6', '0', '4', '9', '0', '5', '1', '5', '3', '5', '7', '0', '0', '2', '5', '1', '5', '8', '2', '2', '3', '3', '9', '9', '1', '0', '0', '0', '0', '0', '6', '2', '9', '9', '8', '2', '7', '0', '8', '1', '7', '9', '9', '4', '0', '8', '9', '1']
noncomputable def geometryRow128_jensenBoundText : String := String.ofList (geometryRow128_jensenBoundNumeratorChars ++ '/' :: geometryRow128_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_jensenBound_before_field"
  err.flush

theorem geometryRow128_jensenBound_field :
    geometryRowsJson128.getObjVal? "jensen_bound" = .ok (.str geometryRow128_jensenBoundText) := by rfl

theorem geometryRow128_jensenBound_numerator_no_slash :
    geometryRow128_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow128_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow128_jensenBoundNumeratorChars = some (28010253285786309839431954807887126064390623481669362134750567908581037029743122799881381076278800000000000000000000 : Int) := by decide +kernel

theorem geometryRow128_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow128_jensenBoundDenominatorChars = some (7146856884517301257881666263294836553700925647271287366801458150360983202333775736319604905153570025158223399100000629982708179940891 : Int) := by decide +kernel

theorem geometryRow128_jensenBound_denominator_nonzero : (7146856884517301257881666263294836553700925647271287366801458150360983202333775736319604905153570025158223399100000629982708179940891 : Int) ≠ 0 := by decide +kernel

theorem geometryRow128_jensenBound_parse :
    parseRational geometryRow128_jensenBoundText = .ok geometryRowsTyped128.jensenBound :=
  original_rational_fraction_of_chars geometryRow128_jensenBoundNumeratorChars geometryRow128_jensenBoundDenominatorChars
    (28010253285786309839431954807887126064390623481669362134750567908581037029743122799881381076278800000000000000000000 : Int) (7146856884517301257881666263294836553700925647271287366801458150360983202333775736319604905153570025158223399100000629982708179940891 : Int)
    geometryRow128_jensenBound_numerator_no_slash geometryRow128_jensenBound_numerator_parse
    geometryRow128_jensenBound_denominator_parse geometryRow128_jensenBound_denominator_nonzero

theorem geometryRow128_jensenBound_read :
    rationalField geometryRowsJson128 "jensen_bound" = .ok geometryRowsTyped128.jensenBound :=
  original_rationalField_of_string geometryRowsJson128 "jensen_bound" geometryRow128_jensenBoundText
    geometryRowsTyped128.jensenBound geometryRow128_jensenBound_field geometryRow128_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_factorMaxima_before"
  err.flush

theorem geometryRow128_factorMaxima_read :
    rationalArrayField geometryRowsJson128 "factor_maxima" = .ok geometryRowsTyped128.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_gapWeightedMeans_before"
  err.flush

theorem geometryRow128_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson128 "gap_weighted_means" = .ok geometryRowsTyped128.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow128_floorChars : List Char := ['3', '1', '0', '5', '1', '4', '2', '4', '9', '1', '6', '5']
noncomputable def geometryRow128_floorText : String := String.ofList geometryRow128_floorChars

theorem geometryRow128_floor_text_read :
    geometryRowsJson128.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow128_floorText := by rfl

theorem geometryRow128_floor_chars_parse :
    SourceJson.intChars geometryRow128_floorChars = some (310514249165 : Int) := by decide +kernel

theorem geometryRow128_floor_parse :
    parseInteger geometryRow128_floorText = .ok geometryRowsTyped128.jensenFloorQ96 := by
  simp only [geometryRow128_floorText, parseInteger, String.toList_ofList, geometryRow128_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_128 :
    decodeGeometryRow geometryRowsJson128 = .ok geometryRowsTyped128 :=
  original_geometryRow_of_fields geometryRowsJson128 geometryRowsTyped128 geometryRow128_floorText
    geometryRow128_simplexId_read geometryRow128_vertexIds_read
    geometryRow128_physicalVolume_read geometryRow128_meanGap_read
    geometryRow128_factorMaxima_read geometryRow128_gapWeightedMeans_read
    geometryRow128_jensenBound_read geometryRow128_floor_text_read geometryRow128_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_128_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson129 : SourceJson :=
  (SimplicesBlock065.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped129 : GeometryRow :=
  { simplexId := 129,
    vertexIds := #[39, 38, 34, 32, 24, 23, 21, 20, 16],
    physicalVolume := ((46859239990298635337817381860479122497789 : ℚ) / (65552798245036032000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((496879 : ℚ) / (5600000 : ℚ)), ((496879 : ℚ) / (5600000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((5577817 : ℚ) / (108000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((18020448583297 : ℚ) / (262006200000000 : ℚ)), ((18069371650807 : ℚ) / (262006200000000 : ℚ)), ((118470279208739 : ℚ) / (786018600000000 : ℚ)), ((9573231913429 : ℚ) / (87335400000000 : ℚ)), ((44494803914629 : ℚ) / (786018600000000 : ℚ)), ((34652066544427 : ℚ) / (786018600000000 : ℚ)), ((352315481041 : ℚ) / (8273880000000 : ℚ)), ((264402098221 : ℚ) / (6288148800000 : ℚ)), ((16303177415689 : ℚ) / (393009300000000 : ℚ)), ((16303151215069 : ℚ) / (393009300000000 : ℚ))],
    jensenBound := ((340047264624188724712239660851731203122318277912783032466962060864489377301338017286814043706695000000000000000000 : ℚ) / (690798828920996118040958329177137575953031746218840358541777786889741522142028359572121030710776185562213498049809439348550248320783 : ℚ)),
    jensenFloorQ96 := (39000239746 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_simplexId_before"
  err.flush

theorem geometryRow129_simplexId_read :
    geometryRowsJson129.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped129.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_vertexIds_before"
  err.flush

theorem geometryRow129_vertexIds_read :
    geometryRowsJson129.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped129.vertexIds := by decide +kernel

noncomputable def geometryRow129_physicalVolumeNumeratorChars : List Char := ['4', '6', '8', '5', '9', '2', '3', '9', '9', '9', '0', '2', '9', '8', '6', '3', '5', '3', '3', '7', '8', '1', '7', '3', '8', '1', '8', '6', '0', '4', '7', '9', '1', '2', '2', '4', '9', '7', '7', '8', '9']
noncomputable def geometryRow129_physicalVolumeDenominatorChars : List Char := ['6', '5', '5', '5', '2', '7', '9', '8', '2', '4', '5', '0', '3', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow129_physicalVolumeText : String := String.ofList (geometryRow129_physicalVolumeNumeratorChars ++ '/' :: geometryRow129_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_physicalVolume_before_field"
  err.flush

theorem geometryRow129_physicalVolume_field :
    geometryRowsJson129.getObjVal? "physical_volume" = .ok (.str geometryRow129_physicalVolumeText) := by rfl

theorem geometryRow129_physicalVolume_numerator_no_slash :
    geometryRow129_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow129_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow129_physicalVolumeNumeratorChars = some (46859239990298635337817381860479122497789 : Int) := by decide +kernel

theorem geometryRow129_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow129_physicalVolumeDenominatorChars = some (65552798245036032000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow129_physicalVolume_denominator_nonzero : (65552798245036032000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow129_physicalVolume_parse :
    parseRational geometryRow129_physicalVolumeText = .ok geometryRowsTyped129.physicalVolume :=
  original_rational_fraction_of_chars geometryRow129_physicalVolumeNumeratorChars geometryRow129_physicalVolumeDenominatorChars
    (46859239990298635337817381860479122497789 : Int) (65552798245036032000000000000000000000000000000000000000000000000000 : Int)
    geometryRow129_physicalVolume_numerator_no_slash geometryRow129_physicalVolume_numerator_parse
    geometryRow129_physicalVolume_denominator_parse geometryRow129_physicalVolume_denominator_nonzero

theorem geometryRow129_physicalVolume_read :
    rationalField geometryRowsJson129 "physical_volume" = .ok geometryRowsTyped129.physicalVolume :=
  original_rationalField_of_string geometryRowsJson129 "physical_volume" geometryRow129_physicalVolumeText
    geometryRowsTyped129.physicalVolume geometryRow129_physicalVolume_field geometryRow129_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_physicalVolume_complete"
  err.flush

noncomputable def geometryRow129_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow129_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow129_meanGapText : String := String.ofList (geometryRow129_meanGapNumeratorChars ++ '/' :: geometryRow129_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_meanGap_before_field"
  err.flush

theorem geometryRow129_meanGap_field :
    geometryRowsJson129.getObjVal? "mean_gap" = .ok (.str geometryRow129_meanGapText) := by rfl

theorem geometryRow129_meanGap_numerator_no_slash :
    geometryRow129_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow129_meanGap_numerator_parse :
    SourceJson.intChars geometryRow129_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow129_meanGap_denominator_parse :
    SourceJson.intChars geometryRow129_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow129_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow129_meanGap_parse :
    parseRational geometryRow129_meanGapText = .ok geometryRowsTyped129.meanGap :=
  original_rational_fraction_of_chars geometryRow129_meanGapNumeratorChars geometryRow129_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow129_meanGap_numerator_no_slash geometryRow129_meanGap_numerator_parse
    geometryRow129_meanGap_denominator_parse geometryRow129_meanGap_denominator_nonzero

theorem geometryRow129_meanGap_read :
    rationalField geometryRowsJson129 "mean_gap" = .ok geometryRowsTyped129.meanGap :=
  original_rationalField_of_string geometryRowsJson129 "mean_gap" geometryRow129_meanGapText
    geometryRowsTyped129.meanGap geometryRow129_meanGap_field geometryRow129_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_meanGap_complete"
  err.flush

noncomputable def geometryRow129_jensenBoundNumeratorChars : List Char := ['3', '4', '0', '0', '4', '7', '2', '6', '4', '6', '2', '4', '1', '8', '8', '7', '2', '4', '7', '1', '2', '2', '3', '9', '6', '6', '0', '8', '5', '1', '7', '3', '1', '2', '0', '3', '1', '2', '2', '3', '1', '8', '2', '7', '7', '9', '1', '2', '7', '8', '3', '0', '3', '2', '4', '6', '6', '9', '6', '2', '0', '6', '0', '8', '6', '4', '4', '8', '9', '3', '7', '7', '3', '0', '1', '3', '3', '8', '0', '1', '7', '2', '8', '6', '8', '1', '4', '0', '4', '3', '7', '0', '6', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow129_jensenBoundDenominatorChars : List Char := ['6', '9', '0', '7', '9', '8', '8', '2', '8', '9', '2', '0', '9', '9', '6', '1', '1', '8', '0', '4', '0', '9', '5', '8', '3', '2', '9', '1', '7', '7', '1', '3', '7', '5', '7', '5', '9', '5', '3', '0', '3', '1', '7', '4', '6', '2', '1', '8', '8', '4', '0', '3', '5', '8', '5', '4', '1', '7', '7', '7', '7', '8', '6', '8', '8', '9', '7', '4', '1', '5', '2', '2', '1', '4', '2', '0', '2', '8', '3', '5', '9', '5', '7', '2', '1', '2', '1', '0', '3', '0', '7', '1', '0', '7', '7', '6', '1', '8', '5', '5', '6', '2', '2', '1', '3', '4', '9', '8', '0', '4', '9', '8', '0', '9', '4', '3', '9', '3', '4', '8', '5', '5', '0', '2', '4', '8', '3', '2', '0', '7', '8', '3']
noncomputable def geometryRow129_jensenBoundText : String := String.ofList (geometryRow129_jensenBoundNumeratorChars ++ '/' :: geometryRow129_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_jensenBound_before_field"
  err.flush

theorem geometryRow129_jensenBound_field :
    geometryRowsJson129.getObjVal? "jensen_bound" = .ok (.str geometryRow129_jensenBoundText) := by rfl

theorem geometryRow129_jensenBound_numerator_no_slash :
    geometryRow129_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow129_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow129_jensenBoundNumeratorChars = some (340047264624188724712239660851731203122318277912783032466962060864489377301338017286814043706695000000000000000000 : Int) := by decide +kernel

theorem geometryRow129_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow129_jensenBoundDenominatorChars = some (690798828920996118040958329177137575953031746218840358541777786889741522142028359572121030710776185562213498049809439348550248320783 : Int) := by decide +kernel

theorem geometryRow129_jensenBound_denominator_nonzero : (690798828920996118040958329177137575953031746218840358541777786889741522142028359572121030710776185562213498049809439348550248320783 : Int) ≠ 0 := by decide +kernel

theorem geometryRow129_jensenBound_parse :
    parseRational geometryRow129_jensenBoundText = .ok geometryRowsTyped129.jensenBound :=
  original_rational_fraction_of_chars geometryRow129_jensenBoundNumeratorChars geometryRow129_jensenBoundDenominatorChars
    (340047264624188724712239660851731203122318277912783032466962060864489377301338017286814043706695000000000000000000 : Int) (690798828920996118040958329177137575953031746218840358541777786889741522142028359572121030710776185562213498049809439348550248320783 : Int)
    geometryRow129_jensenBound_numerator_no_slash geometryRow129_jensenBound_numerator_parse
    geometryRow129_jensenBound_denominator_parse geometryRow129_jensenBound_denominator_nonzero

theorem geometryRow129_jensenBound_read :
    rationalField geometryRowsJson129 "jensen_bound" = .ok geometryRowsTyped129.jensenBound :=
  original_rationalField_of_string geometryRowsJson129 "jensen_bound" geometryRow129_jensenBoundText
    geometryRowsTyped129.jensenBound geometryRow129_jensenBound_field geometryRow129_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_factorMaxima_before"
  err.flush

theorem geometryRow129_factorMaxima_read :
    rationalArrayField geometryRowsJson129 "factor_maxima" = .ok geometryRowsTyped129.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_gapWeightedMeans_before"
  err.flush

theorem geometryRow129_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson129 "gap_weighted_means" = .ok geometryRowsTyped129.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow129_floorChars : List Char := ['3', '9', '0', '0', '0', '2', '3', '9', '7', '4', '6']
noncomputable def geometryRow129_floorText : String := String.ofList geometryRow129_floorChars

theorem geometryRow129_floor_text_read :
    geometryRowsJson129.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow129_floorText := by rfl

theorem geometryRow129_floor_chars_parse :
    SourceJson.intChars geometryRow129_floorChars = some (39000239746 : Int) := by decide +kernel

theorem geometryRow129_floor_parse :
    parseInteger geometryRow129_floorText = .ok geometryRowsTyped129.jensenFloorQ96 := by
  simp only [geometryRow129_floorText, parseInteger, String.toList_ofList, geometryRow129_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_129 :
    decodeGeometryRow geometryRowsJson129 = .ok geometryRowsTyped129 :=
  original_geometryRow_of_fields geometryRowsJson129 geometryRowsTyped129 geometryRow129_floorText
    geometryRow129_simplexId_read geometryRow129_vertexIds_read
    geometryRow129_physicalVolume_read geometryRow129_meanGap_read
    geometryRow129_factorMaxima_read geometryRow129_gapWeightedMeans_read
    geometryRow129_jensenBound_read geometryRow129_floor_text_read geometryRow129_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_129_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock065 : List SourceJson := [geometryRowsJson128, geometryRowsJson129]
noncomputable def geometryRowsTypedBlock065 : List (GeometryRow) := [geometryRowsTyped128, geometryRowsTyped129]
noncomputable def geometryRowsTypedThroughBlock065 : List (GeometryRow) := geometryRowsTypedThroughBlock064 ++ geometryRowsTypedBlock065

theorem geometry_Rows_block_065_push_eq (acc : List SourceJson) :
    SimplicesBlock065.blockPush acc = [geometryRowsJson129, geometryRowsJson128] ++ acc := by rfl

theorem geometry_Rows_block_065_reverse (acc : List SourceJson) :
    (SimplicesBlock065.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock065 := by
  rw [geometry_Rows_block_065_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_065 :
    geometryRowsJsonBlock065.mapM decodeGeometryRow = .ok geometryRowsTypedBlock065 := by
  simp only [geometryRowsJsonBlock065, geometryRowsTypedBlock065, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_128, decode_geometry_Rows_129]
  rfl

theorem decode_geometry_Rows_through_block_065 :
    SimplicesValue.arrayAcc066.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock065 := by
  change (SimplicesBlock065.blockPush SimplicesValue.arrayAcc065).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_065_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_064, decode_geometry_Rows_block_065]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_065_complete"
  err.flush

#print axioms geometryRow128_simplexId_read
#print axioms geometryRow128_vertexIds_read
#print axioms geometryRow128_physicalVolume_field
#print axioms geometryRow128_physicalVolume_numerator_no_slash
#print axioms geometryRow128_physicalVolume_numerator_parse
#print axioms geometryRow128_physicalVolume_denominator_parse
#print axioms geometryRow128_physicalVolume_denominator_nonzero
#print axioms geometryRow128_physicalVolume_parse
#print axioms geometryRow128_physicalVolume_read
#print axioms geometryRow128_meanGap_field
#print axioms geometryRow128_meanGap_numerator_no_slash
#print axioms geometryRow128_meanGap_numerator_parse
#print axioms geometryRow128_meanGap_denominator_parse
#print axioms geometryRow128_meanGap_denominator_nonzero
#print axioms geometryRow128_meanGap_parse
#print axioms geometryRow128_meanGap_read
#print axioms geometryRow128_jensenBound_field
#print axioms geometryRow128_jensenBound_numerator_no_slash
#print axioms geometryRow128_jensenBound_numerator_parse
#print axioms geometryRow128_jensenBound_denominator_parse
#print axioms geometryRow128_jensenBound_denominator_nonzero
#print axioms geometryRow128_jensenBound_parse
#print axioms geometryRow128_jensenBound_read
#print axioms geometryRow128_factorMaxima_read
#print axioms geometryRow128_gapWeightedMeans_read
#print axioms geometryRow128_floor_text_read
#print axioms geometryRow128_floor_chars_parse
#print axioms geometryRow128_floor_parse
#print axioms decode_geometry_Rows_128
#print axioms geometryRow129_simplexId_read
#print axioms geometryRow129_vertexIds_read
#print axioms geometryRow129_physicalVolume_field
#print axioms geometryRow129_physicalVolume_numerator_no_slash
#print axioms geometryRow129_physicalVolume_numerator_parse
#print axioms geometryRow129_physicalVolume_denominator_parse
#print axioms geometryRow129_physicalVolume_denominator_nonzero
#print axioms geometryRow129_physicalVolume_parse
#print axioms geometryRow129_physicalVolume_read
#print axioms geometryRow129_meanGap_field
#print axioms geometryRow129_meanGap_numerator_no_slash
#print axioms geometryRow129_meanGap_numerator_parse
#print axioms geometryRow129_meanGap_denominator_parse
#print axioms geometryRow129_meanGap_denominator_nonzero
#print axioms geometryRow129_meanGap_parse
#print axioms geometryRow129_meanGap_read
#print axioms geometryRow129_jensenBound_field
#print axioms geometryRow129_jensenBound_numerator_no_slash
#print axioms geometryRow129_jensenBound_numerator_parse
#print axioms geometryRow129_jensenBound_denominator_parse
#print axioms geometryRow129_jensenBound_denominator_nonzero
#print axioms geometryRow129_jensenBound_parse
#print axioms geometryRow129_jensenBound_read
#print axioms geometryRow129_factorMaxima_read
#print axioms geometryRow129_gapWeightedMeans_read
#print axioms geometryRow129_floor_text_read
#print axioms geometryRow129_floor_chars_parse
#print axioms geometryRow129_floor_parse
#print axioms decode_geometry_Rows_129
#print axioms geometry_Rows_block_065_push_eq
#print axioms geometry_Rows_block_065_reverse
#print axioms decode_geometry_Rows_block_065
#print axioms decode_geometry_Rows_through_block_065

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
