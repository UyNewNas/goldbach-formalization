import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows058

/-! Original simplices typed block 59, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson116 : SourceJson :=
  (SimplicesBlock059.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped116 : GeometryRow :=
  { simplexId := 116,
    vertexIds := #[39, 37, 31, 24, 23, 21, 19, 18, 15],
    physicalVolume := ((18473773249365113899602003993244632186990749 : ℚ) / (3288981374083399680000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((1115573 : ℚ) / (21600000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((229932560216119 : ℚ) / (3128000400000000 : ℚ)), ((230617591178539 : ℚ) / (3128000400000000 : ℚ)), ((465196518557921 : ℚ) / (3128000400000000 : ℚ)), ((250202262799693 : ℚ) / (2346000300000000 : ℚ)), ((155813142829261 : ℚ) / (3128000400000000 : ℚ)), ((143274586043383 : ℚ) / (3128000400000000 : ℚ)), ((4338552912403 : ℚ) / (98778960000000 : ℚ)), ((81430354921189 : ℚ) / (1876800240000000 : ℚ)), ((403024023226991 : ℚ) / (9384001200000000 : ℚ)), ((398909458251911 : ℚ) / (9384001200000000 : ℚ))],
    jensenBound := ((31350592590020203044100731560721544589661107903529694847648633369166888799074589687075322468546423138942400000000000000000000000 : ℚ) / (7825828737263459132812909604614291851823289124068454061427413619232236645390477401057925320046755280838424971108296778137995485248264690090933 : ℚ)),
    jensenFloorQ96 := (317391285706715 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_simplexId_before"
  err.flush

theorem geometryRow116_simplexId_read :
    geometryRowsJson116.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped116.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_vertexIds_before"
  err.flush

theorem geometryRow116_vertexIds_read :
    geometryRowsJson116.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped116.vertexIds := by decide +kernel

noncomputable def geometryRow116_physicalVolumeNumeratorChars : List Char := ['1', '8', '4', '7', '3', '7', '7', '3', '2', '4', '9', '3', '6', '5', '1', '1', '3', '8', '9', '9', '6', '0', '2', '0', '0', '3', '9', '9', '3', '2', '4', '4', '6', '3', '2', '1', '8', '6', '9', '9', '0', '7', '4', '9']
noncomputable def geometryRow116_physicalVolumeDenominatorChars : List Char := ['3', '2', '8', '8', '9', '8', '1', '3', '7', '4', '0', '8', '3', '3', '9', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow116_physicalVolumeText : String := String.ofList (geometryRow116_physicalVolumeNumeratorChars ++ '/' :: geometryRow116_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_physicalVolume_before_field"
  err.flush

theorem geometryRow116_physicalVolume_field :
    geometryRowsJson116.getObjVal? "physical_volume" = .ok (.str geometryRow116_physicalVolumeText) := by rfl

theorem geometryRow116_physicalVolume_numerator_no_slash :
    geometryRow116_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow116_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow116_physicalVolumeNumeratorChars = some (18473773249365113899602003993244632186990749 : Int) := by decide +kernel

theorem geometryRow116_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow116_physicalVolumeDenominatorChars = some (3288981374083399680000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow116_physicalVolume_denominator_nonzero : (3288981374083399680000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow116_physicalVolume_parse :
    parseRational geometryRow116_physicalVolumeText = .ok geometryRowsTyped116.physicalVolume :=
  original_rational_fraction_of_chars geometryRow116_physicalVolumeNumeratorChars geometryRow116_physicalVolumeDenominatorChars
    (18473773249365113899602003993244632186990749 : Int) (3288981374083399680000000000000000000000000000000000000000000000000 : Int)
    geometryRow116_physicalVolume_numerator_no_slash geometryRow116_physicalVolume_numerator_parse
    geometryRow116_physicalVolume_denominator_parse geometryRow116_physicalVolume_denominator_nonzero

theorem geometryRow116_physicalVolume_read :
    rationalField geometryRowsJson116 "physical_volume" = .ok geometryRowsTyped116.physicalVolume :=
  original_rationalField_of_string geometryRowsJson116 "physical_volume" geometryRow116_physicalVolumeText
    geometryRowsTyped116.physicalVolume geometryRow116_physicalVolume_field geometryRow116_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_physicalVolume_complete"
  err.flush

noncomputable def geometryRow116_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow116_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow116_meanGapText : String := String.ofList (geometryRow116_meanGapNumeratorChars ++ '/' :: geometryRow116_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_meanGap_before_field"
  err.flush

theorem geometryRow116_meanGap_field :
    geometryRowsJson116.getObjVal? "mean_gap" = .ok (.str geometryRow116_meanGapText) := by rfl

theorem geometryRow116_meanGap_numerator_no_slash :
    geometryRow116_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow116_meanGap_numerator_parse :
    SourceJson.intChars geometryRow116_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow116_meanGap_denominator_parse :
    SourceJson.intChars geometryRow116_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow116_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow116_meanGap_parse :
    parseRational geometryRow116_meanGapText = .ok geometryRowsTyped116.meanGap :=
  original_rational_fraction_of_chars geometryRow116_meanGapNumeratorChars geometryRow116_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow116_meanGap_numerator_no_slash geometryRow116_meanGap_numerator_parse
    geometryRow116_meanGap_denominator_parse geometryRow116_meanGap_denominator_nonzero

theorem geometryRow116_meanGap_read :
    rationalField geometryRowsJson116 "mean_gap" = .ok geometryRowsTyped116.meanGap :=
  original_rationalField_of_string geometryRowsJson116 "mean_gap" geometryRow116_meanGapText
    geometryRowsTyped116.meanGap geometryRow116_meanGap_field geometryRow116_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_meanGap_complete"
  err.flush

noncomputable def geometryRow116_jensenBoundNumeratorChars : List Char := ['3', '1', '3', '5', '0', '5', '9', '2', '5', '9', '0', '0', '2', '0', '2', '0', '3', '0', '4', '4', '1', '0', '0', '7', '3', '1', '5', '6', '0', '7', '2', '1', '5', '4', '4', '5', '8', '9', '6', '6', '1', '1', '0', '7', '9', '0', '3', '5', '2', '9', '6', '9', '4', '8', '4', '7', '6', '4', '8', '6', '3', '3', '3', '6', '9', '1', '6', '6', '8', '8', '8', '7', '9', '9', '0', '7', '4', '5', '8', '9', '6', '8', '7', '0', '7', '5', '3', '2', '2', '4', '6', '8', '5', '4', '6', '4', '2', '3', '1', '3', '8', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow116_jensenBoundDenominatorChars : List Char := ['7', '8', '2', '5', '8', '2', '8', '7', '3', '7', '2', '6', '3', '4', '5', '9', '1', '3', '2', '8', '1', '2', '9', '0', '9', '6', '0', '4', '6', '1', '4', '2', '9', '1', '8', '5', '1', '8', '2', '3', '2', '8', '9', '1', '2', '4', '0', '6', '8', '4', '5', '4', '0', '6', '1', '4', '2', '7', '4', '1', '3', '6', '1', '9', '2', '3', '2', '2', '3', '6', '6', '4', '5', '3', '9', '0', '4', '7', '7', '4', '0', '1', '0', '5', '7', '9', '2', '5', '3', '2', '0', '0', '4', '6', '7', '5', '5', '2', '8', '0', '8', '3', '8', '4', '2', '4', '9', '7', '1', '1', '0', '8', '2', '9', '6', '7', '7', '8', '1', '3', '7', '9', '9', '5', '4', '8', '5', '2', '4', '8', '2', '6', '4', '6', '9', '0', '0', '9', '0', '9', '3', '3']
noncomputable def geometryRow116_jensenBoundText : String := String.ofList (geometryRow116_jensenBoundNumeratorChars ++ '/' :: geometryRow116_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_jensenBound_before_field"
  err.flush

theorem geometryRow116_jensenBound_field :
    geometryRowsJson116.getObjVal? "jensen_bound" = .ok (.str geometryRow116_jensenBoundText) := by rfl

theorem geometryRow116_jensenBound_numerator_no_slash :
    geometryRow116_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow116_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow116_jensenBoundNumeratorChars = some (31350592590020203044100731560721544589661107903529694847648633369166888799074589687075322468546423138942400000000000000000000000 : Int) := by decide +kernel

theorem geometryRow116_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow116_jensenBoundDenominatorChars = some (7825828737263459132812909604614291851823289124068454061427413619232236645390477401057925320046755280838424971108296778137995485248264690090933 : Int) := by decide +kernel

theorem geometryRow116_jensenBound_denominator_nonzero : (7825828737263459132812909604614291851823289124068454061427413619232236645390477401057925320046755280838424971108296778137995485248264690090933 : Int) ≠ 0 := by decide +kernel

theorem geometryRow116_jensenBound_parse :
    parseRational geometryRow116_jensenBoundText = .ok geometryRowsTyped116.jensenBound :=
  original_rational_fraction_of_chars geometryRow116_jensenBoundNumeratorChars geometryRow116_jensenBoundDenominatorChars
    (31350592590020203044100731560721544589661107903529694847648633369166888799074589687075322468546423138942400000000000000000000000 : Int) (7825828737263459132812909604614291851823289124068454061427413619232236645390477401057925320046755280838424971108296778137995485248264690090933 : Int)
    geometryRow116_jensenBound_numerator_no_slash geometryRow116_jensenBound_numerator_parse
    geometryRow116_jensenBound_denominator_parse geometryRow116_jensenBound_denominator_nonzero

theorem geometryRow116_jensenBound_read :
    rationalField geometryRowsJson116 "jensen_bound" = .ok geometryRowsTyped116.jensenBound :=
  original_rationalField_of_string geometryRowsJson116 "jensen_bound" geometryRow116_jensenBoundText
    geometryRowsTyped116.jensenBound geometryRow116_jensenBound_field geometryRow116_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_factorMaxima_before"
  err.flush

theorem geometryRow116_factorMaxima_read :
    rationalArrayField geometryRowsJson116 "factor_maxima" = .ok geometryRowsTyped116.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_gapWeightedMeans_before"
  err.flush

theorem geometryRow116_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson116 "gap_weighted_means" = .ok geometryRowsTyped116.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow116_floorChars : List Char := ['3', '1', '7', '3', '9', '1', '2', '8', '5', '7', '0', '6', '7', '1', '5']
noncomputable def geometryRow116_floorText : String := String.ofList geometryRow116_floorChars

theorem geometryRow116_floor_text_read :
    geometryRowsJson116.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow116_floorText := by rfl

theorem geometryRow116_floor_chars_parse :
    SourceJson.intChars geometryRow116_floorChars = some (317391285706715 : Int) := by decide +kernel

theorem geometryRow116_floor_parse :
    parseInteger geometryRow116_floorText = .ok geometryRowsTyped116.jensenFloorQ96 := by
  simp only [geometryRow116_floorText, parseInteger, String.toList_ofList, geometryRow116_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_116 :
    decodeGeometryRow geometryRowsJson116 = .ok geometryRowsTyped116 :=
  original_geometryRow_of_fields geometryRowsJson116 geometryRowsTyped116 geometryRow116_floorText
    geometryRow116_simplexId_read geometryRow116_vertexIds_read
    geometryRow116_physicalVolume_read geometryRow116_meanGap_read
    geometryRow116_factorMaxima_read geometryRow116_gapWeightedMeans_read
    geometryRow116_jensenBound_read geometryRow116_floor_text_read geometryRow116_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_116_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson117 : SourceJson :=
  (SimplicesBlock059.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped117 : GeometryRow :=
  { simplexId := 117,
    vertexIds := #[39, 37, 31, 24, 22, 19, 18, 15, 14],
    physicalVolume := ((103237992195238023144135963395968436479279 : ℚ) / (17541725071091171328000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((734331 : ℚ) / (14000000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((140550916411 : ℚ) / (1901520000000 : ℚ)), ((140967348607 : ℚ) / (1901520000000 : ℚ)), ((56474379889 : ℚ) / (380304000000 : ℚ)), ((1069986983293 : ℚ) / (9982980000000 : ℚ)), ((665416362787 : ℚ) / (13310640000000 : ℚ)), ((87765625927 : ℚ) / (1901520000000 : ℚ)), ((351307768711 : ℚ) / (7986384000000 : ℚ)), ((1713890782379 : ℚ) / (39931920000000 : ℚ)), ((1713888120251 : ℚ) / (39931920000000 : ℚ)), ((333486394249 : ℚ) / (7986384000000 : ℚ))],
    jensenBound := ((71225834311408998222822810709380161328515610675939051205724244459710282713558302720000000000000 : ℚ) / (16933140671344294510558908135081191119188513006299875317712908185025320445928531134270022727752360391747485738031 : ℚ)),
    jensenFloorQ96 := (333257254845 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_simplexId_before"
  err.flush

theorem geometryRow117_simplexId_read :
    geometryRowsJson117.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped117.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_vertexIds_before"
  err.flush

theorem geometryRow117_vertexIds_read :
    geometryRowsJson117.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped117.vertexIds := by decide +kernel

noncomputable def geometryRow117_physicalVolumeNumeratorChars : List Char := ['1', '0', '3', '2', '3', '7', '9', '9', '2', '1', '9', '5', '2', '3', '8', '0', '2', '3', '1', '4', '4', '1', '3', '5', '9', '6', '3', '3', '9', '5', '9', '6', '8', '4', '3', '6', '4', '7', '9', '2', '7', '9']
noncomputable def geometryRow117_physicalVolumeDenominatorChars : List Char := ['1', '7', '5', '4', '1', '7', '2', '5', '0', '7', '1', '0', '9', '1', '1', '7', '1', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow117_physicalVolumeText : String := String.ofList (geometryRow117_physicalVolumeNumeratorChars ++ '/' :: geometryRow117_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_physicalVolume_before_field"
  err.flush

theorem geometryRow117_physicalVolume_field :
    geometryRowsJson117.getObjVal? "physical_volume" = .ok (.str geometryRow117_physicalVolumeText) := by rfl

theorem geometryRow117_physicalVolume_numerator_no_slash :
    geometryRow117_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow117_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow117_physicalVolumeNumeratorChars = some (103237992195238023144135963395968436479279 : Int) := by decide +kernel

theorem geometryRow117_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow117_physicalVolumeDenominatorChars = some (17541725071091171328000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow117_physicalVolume_denominator_nonzero : (17541725071091171328000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow117_physicalVolume_parse :
    parseRational geometryRow117_physicalVolumeText = .ok geometryRowsTyped117.physicalVolume :=
  original_rational_fraction_of_chars geometryRow117_physicalVolumeNumeratorChars geometryRow117_physicalVolumeDenominatorChars
    (103237992195238023144135963395968436479279 : Int) (17541725071091171328000000000000000000000000000000000000000000000000 : Int)
    geometryRow117_physicalVolume_numerator_no_slash geometryRow117_physicalVolume_numerator_parse
    geometryRow117_physicalVolume_denominator_parse geometryRow117_physicalVolume_denominator_nonzero

theorem geometryRow117_physicalVolume_read :
    rationalField geometryRowsJson117 "physical_volume" = .ok geometryRowsTyped117.physicalVolume :=
  original_rationalField_of_string geometryRowsJson117 "physical_volume" geometryRow117_physicalVolumeText
    geometryRowsTyped117.physicalVolume geometryRow117_physicalVolume_field geometryRow117_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_physicalVolume_complete"
  err.flush

noncomputable def geometryRow117_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow117_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow117_meanGapText : String := String.ofList (geometryRow117_meanGapNumeratorChars ++ '/' :: geometryRow117_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_meanGap_before_field"
  err.flush

theorem geometryRow117_meanGap_field :
    geometryRowsJson117.getObjVal? "mean_gap" = .ok (.str geometryRow117_meanGapText) := by rfl

theorem geometryRow117_meanGap_numerator_no_slash :
    geometryRow117_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow117_meanGap_numerator_parse :
    SourceJson.intChars geometryRow117_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow117_meanGap_denominator_parse :
    SourceJson.intChars geometryRow117_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow117_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow117_meanGap_parse :
    parseRational geometryRow117_meanGapText = .ok geometryRowsTyped117.meanGap :=
  original_rational_fraction_of_chars geometryRow117_meanGapNumeratorChars geometryRow117_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow117_meanGap_numerator_no_slash geometryRow117_meanGap_numerator_parse
    geometryRow117_meanGap_denominator_parse geometryRow117_meanGap_denominator_nonzero

theorem geometryRow117_meanGap_read :
    rationalField geometryRowsJson117 "mean_gap" = .ok geometryRowsTyped117.meanGap :=
  original_rationalField_of_string geometryRowsJson117 "mean_gap" geometryRow117_meanGapText
    geometryRowsTyped117.meanGap geometryRow117_meanGap_field geometryRow117_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_meanGap_complete"
  err.flush

noncomputable def geometryRow117_jensenBoundNumeratorChars : List Char := ['7', '1', '2', '2', '5', '8', '3', '4', '3', '1', '1', '4', '0', '8', '9', '9', '8', '2', '2', '2', '8', '2', '2', '8', '1', '0', '7', '0', '9', '3', '8', '0', '1', '6', '1', '3', '2', '8', '5', '1', '5', '6', '1', '0', '6', '7', '5', '9', '3', '9', '0', '5', '1', '2', '0', '5', '7', '2', '4', '2', '4', '4', '4', '5', '9', '7', '1', '0', '2', '8', '2', '7', '1', '3', '5', '5', '8', '3', '0', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow117_jensenBoundDenominatorChars : List Char := ['1', '6', '9', '3', '3', '1', '4', '0', '6', '7', '1', '3', '4', '4', '2', '9', '4', '5', '1', '0', '5', '5', '8', '9', '0', '8', '1', '3', '5', '0', '8', '1', '1', '9', '1', '1', '1', '9', '1', '8', '8', '5', '1', '3', '0', '0', '6', '2', '9', '9', '8', '7', '5', '3', '1', '7', '7', '1', '2', '9', '0', '8', '1', '8', '5', '0', '2', '5', '3', '2', '0', '4', '4', '5', '9', '2', '8', '5', '3', '1', '1', '3', '4', '2', '7', '0', '0', '2', '2', '7', '2', '7', '7', '5', '2', '3', '6', '0', '3', '9', '1', '7', '4', '7', '4', '8', '5', '7', '3', '8', '0', '3', '1']
noncomputable def geometryRow117_jensenBoundText : String := String.ofList (geometryRow117_jensenBoundNumeratorChars ++ '/' :: geometryRow117_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_jensenBound_before_field"
  err.flush

theorem geometryRow117_jensenBound_field :
    geometryRowsJson117.getObjVal? "jensen_bound" = .ok (.str geometryRow117_jensenBoundText) := by rfl

theorem geometryRow117_jensenBound_numerator_no_slash :
    geometryRow117_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow117_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow117_jensenBoundNumeratorChars = some (71225834311408998222822810709380161328515610675939051205724244459710282713558302720000000000000 : Int) := by decide +kernel

theorem geometryRow117_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow117_jensenBoundDenominatorChars = some (16933140671344294510558908135081191119188513006299875317712908185025320445928531134270022727752360391747485738031 : Int) := by decide +kernel

theorem geometryRow117_jensenBound_denominator_nonzero : (16933140671344294510558908135081191119188513006299875317712908185025320445928531134270022727752360391747485738031 : Int) ≠ 0 := by decide +kernel

theorem geometryRow117_jensenBound_parse :
    parseRational geometryRow117_jensenBoundText = .ok geometryRowsTyped117.jensenBound :=
  original_rational_fraction_of_chars geometryRow117_jensenBoundNumeratorChars geometryRow117_jensenBoundDenominatorChars
    (71225834311408998222822810709380161328515610675939051205724244459710282713558302720000000000000 : Int) (16933140671344294510558908135081191119188513006299875317712908185025320445928531134270022727752360391747485738031 : Int)
    geometryRow117_jensenBound_numerator_no_slash geometryRow117_jensenBound_numerator_parse
    geometryRow117_jensenBound_denominator_parse geometryRow117_jensenBound_denominator_nonzero

theorem geometryRow117_jensenBound_read :
    rationalField geometryRowsJson117 "jensen_bound" = .ok geometryRowsTyped117.jensenBound :=
  original_rationalField_of_string geometryRowsJson117 "jensen_bound" geometryRow117_jensenBoundText
    geometryRowsTyped117.jensenBound geometryRow117_jensenBound_field geometryRow117_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_factorMaxima_before"
  err.flush

theorem geometryRow117_factorMaxima_read :
    rationalArrayField geometryRowsJson117 "factor_maxima" = .ok geometryRowsTyped117.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_gapWeightedMeans_before"
  err.flush

theorem geometryRow117_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson117 "gap_weighted_means" = .ok geometryRowsTyped117.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow117_floorChars : List Char := ['3', '3', '3', '2', '5', '7', '2', '5', '4', '8', '4', '5']
noncomputable def geometryRow117_floorText : String := String.ofList geometryRow117_floorChars

theorem geometryRow117_floor_text_read :
    geometryRowsJson117.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow117_floorText := by rfl

theorem geometryRow117_floor_chars_parse :
    SourceJson.intChars geometryRow117_floorChars = some (333257254845 : Int) := by decide +kernel

theorem geometryRow117_floor_parse :
    parseInteger geometryRow117_floorText = .ok geometryRowsTyped117.jensenFloorQ96 := by
  simp only [geometryRow117_floorText, parseInteger, String.toList_ofList, geometryRow117_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_117 :
    decodeGeometryRow geometryRowsJson117 = .ok geometryRowsTyped117 :=
  original_geometryRow_of_fields geometryRowsJson117 geometryRowsTyped117 geometryRow117_floorText
    geometryRow117_simplexId_read geometryRow117_vertexIds_read
    geometryRow117_physicalVolume_read geometryRow117_meanGap_read
    geometryRow117_factorMaxima_read geometryRow117_gapWeightedMeans_read
    geometryRow117_jensenBound_read geometryRow117_floor_text_read geometryRow117_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_117_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock059 : List SourceJson := [geometryRowsJson116, geometryRowsJson117]
noncomputable def geometryRowsTypedBlock059 : List (GeometryRow) := [geometryRowsTyped116, geometryRowsTyped117]
noncomputable def geometryRowsTypedThroughBlock059 : List (GeometryRow) := geometryRowsTypedThroughBlock058 ++ geometryRowsTypedBlock059

theorem geometry_Rows_block_059_push_eq (acc : List SourceJson) :
    SimplicesBlock059.blockPush acc = [geometryRowsJson117, geometryRowsJson116] ++ acc := by rfl

theorem geometry_Rows_block_059_reverse (acc : List SourceJson) :
    (SimplicesBlock059.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock059 := by
  rw [geometry_Rows_block_059_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_059 :
    geometryRowsJsonBlock059.mapM decodeGeometryRow = .ok geometryRowsTypedBlock059 := by
  simp only [geometryRowsJsonBlock059, geometryRowsTypedBlock059, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_116, decode_geometry_Rows_117]
  rfl

theorem decode_geometry_Rows_through_block_059 :
    SimplicesValue.arrayAcc060.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock059 := by
  change (SimplicesBlock059.blockPush SimplicesValue.arrayAcc059).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_059_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_058, decode_geometry_Rows_block_059]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_059_complete"
  err.flush

#print axioms geometryRow116_simplexId_read
#print axioms geometryRow116_vertexIds_read
#print axioms geometryRow116_physicalVolume_field
#print axioms geometryRow116_physicalVolume_numerator_no_slash
#print axioms geometryRow116_physicalVolume_numerator_parse
#print axioms geometryRow116_physicalVolume_denominator_parse
#print axioms geometryRow116_physicalVolume_denominator_nonzero
#print axioms geometryRow116_physicalVolume_parse
#print axioms geometryRow116_physicalVolume_read
#print axioms geometryRow116_meanGap_field
#print axioms geometryRow116_meanGap_numerator_no_slash
#print axioms geometryRow116_meanGap_numerator_parse
#print axioms geometryRow116_meanGap_denominator_parse
#print axioms geometryRow116_meanGap_denominator_nonzero
#print axioms geometryRow116_meanGap_parse
#print axioms geometryRow116_meanGap_read
#print axioms geometryRow116_jensenBound_field
#print axioms geometryRow116_jensenBound_numerator_no_slash
#print axioms geometryRow116_jensenBound_numerator_parse
#print axioms geometryRow116_jensenBound_denominator_parse
#print axioms geometryRow116_jensenBound_denominator_nonzero
#print axioms geometryRow116_jensenBound_parse
#print axioms geometryRow116_jensenBound_read
#print axioms geometryRow116_factorMaxima_read
#print axioms geometryRow116_gapWeightedMeans_read
#print axioms geometryRow116_floor_text_read
#print axioms geometryRow116_floor_chars_parse
#print axioms geometryRow116_floor_parse
#print axioms decode_geometry_Rows_116
#print axioms geometryRow117_simplexId_read
#print axioms geometryRow117_vertexIds_read
#print axioms geometryRow117_physicalVolume_field
#print axioms geometryRow117_physicalVolume_numerator_no_slash
#print axioms geometryRow117_physicalVolume_numerator_parse
#print axioms geometryRow117_physicalVolume_denominator_parse
#print axioms geometryRow117_physicalVolume_denominator_nonzero
#print axioms geometryRow117_physicalVolume_parse
#print axioms geometryRow117_physicalVolume_read
#print axioms geometryRow117_meanGap_field
#print axioms geometryRow117_meanGap_numerator_no_slash
#print axioms geometryRow117_meanGap_numerator_parse
#print axioms geometryRow117_meanGap_denominator_parse
#print axioms geometryRow117_meanGap_denominator_nonzero
#print axioms geometryRow117_meanGap_parse
#print axioms geometryRow117_meanGap_read
#print axioms geometryRow117_jensenBound_field
#print axioms geometryRow117_jensenBound_numerator_no_slash
#print axioms geometryRow117_jensenBound_numerator_parse
#print axioms geometryRow117_jensenBound_denominator_parse
#print axioms geometryRow117_jensenBound_denominator_nonzero
#print axioms geometryRow117_jensenBound_parse
#print axioms geometryRow117_jensenBound_read
#print axioms geometryRow117_factorMaxima_read
#print axioms geometryRow117_gapWeightedMeans_read
#print axioms geometryRow117_floor_text_read
#print axioms geometryRow117_floor_chars_parse
#print axioms geometryRow117_floor_parse
#print axioms decode_geometry_Rows_117
#print axioms geometry_Rows_block_059_push_eq
#print axioms geometry_Rows_block_059_reverse
#print axioms decode_geometry_Rows_block_059
#print axioms decode_geometry_Rows_through_block_059

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
