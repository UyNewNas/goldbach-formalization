import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows045

/-! Original simplices typed block 46, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson091 : SourceJson :=
  (SimplicesBlock046.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped091 : GeometryRow :=
  { simplexId := 91,
    vertexIds := #[39, 37, 24, 23, 21, 20, 16, 1, 0],
    physicalVolume := ((87366807204727612927625688634195358451497 : ℚ) / (15732671578808647680000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((294668571198803 : ℚ) / (3668086800000000 : ℚ)), ((295353494143943 : ℚ) / (3668086800000000 : ℚ)), ((1605316875984601 : ℚ) / (11004260400000000 : ℚ)), ((96893908646077 : ℚ) / (917021700000000 : ℚ)), ((578346094205741 : ℚ) / (11004260400000000 : ℚ)), ((538395964559723 : ℚ) / (11004260400000000 : ℚ)), ((4829609201957 : ℚ) / (115834320000000 : ℚ)), ((90587391257627 : ℚ) / (2200852080000000 : ℚ)), ((446723719275397 : ℚ) / (11004260400000000 : ℚ)), ((446721518423317 : ℚ) / (11004260400000000 : ℚ))],
    jensenBound := ((1169566198915342514790044212240668689714801022168554536042560180704064084609594588491711372850460337995200000000000000000000000 : ℚ) / (368025921360713313125809333325700120677530360762832505901373172939571066274905551435218124699208677596414009703855386590810957817147825327330809 : ℚ)),
    jensenFloorQ96 := (251782756323 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_simplexId_before"
  err.flush

theorem geometryRow091_simplexId_read :
    geometryRowsJson091.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped091.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_vertexIds_before"
  err.flush

theorem geometryRow091_vertexIds_read :
    geometryRowsJson091.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped091.vertexIds := by decide +kernel

noncomputable def geometryRow091_physicalVolumeNumeratorChars : List Char := ['8', '7', '3', '6', '6', '8', '0', '7', '2', '0', '4', '7', '2', '7', '6', '1', '2', '9', '2', '7', '6', '2', '5', '6', '8', '8', '6', '3', '4', '1', '9', '5', '3', '5', '8', '4', '5', '1', '4', '9', '7']
noncomputable def geometryRow091_physicalVolumeDenominatorChars : List Char := ['1', '5', '7', '3', '2', '6', '7', '1', '5', '7', '8', '8', '0', '8', '6', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow091_physicalVolumeText : String := String.ofList (geometryRow091_physicalVolumeNumeratorChars ++ '/' :: geometryRow091_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_physicalVolume_before_field"
  err.flush

theorem geometryRow091_physicalVolume_field :
    geometryRowsJson091.getObjVal? "physical_volume" = .ok (.str geometryRow091_physicalVolumeText) := by rfl

theorem geometryRow091_physicalVolume_numerator_no_slash :
    geometryRow091_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow091_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow091_physicalVolumeNumeratorChars = some (87366807204727612927625688634195358451497 : Int) := by decide +kernel

theorem geometryRow091_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow091_physicalVolumeDenominatorChars = some (15732671578808647680000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow091_physicalVolume_denominator_nonzero : (15732671578808647680000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow091_physicalVolume_parse :
    parseRational geometryRow091_physicalVolumeText = .ok geometryRowsTyped091.physicalVolume :=
  original_rational_fraction_of_chars geometryRow091_physicalVolumeNumeratorChars geometryRow091_physicalVolumeDenominatorChars
    (87366807204727612927625688634195358451497 : Int) (15732671578808647680000000000000000000000000000000000000000000000000 : Int)
    geometryRow091_physicalVolume_numerator_no_slash geometryRow091_physicalVolume_numerator_parse
    geometryRow091_physicalVolume_denominator_parse geometryRow091_physicalVolume_denominator_nonzero

theorem geometryRow091_physicalVolume_read :
    rationalField geometryRowsJson091 "physical_volume" = .ok geometryRowsTyped091.physicalVolume :=
  original_rationalField_of_string geometryRowsJson091 "physical_volume" geometryRow091_physicalVolumeText
    geometryRowsTyped091.physicalVolume geometryRow091_physicalVolume_field geometryRow091_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_physicalVolume_complete"
  err.flush

noncomputable def geometryRow091_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow091_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow091_meanGapText : String := String.ofList (geometryRow091_meanGapNumeratorChars ++ '/' :: geometryRow091_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_meanGap_before_field"
  err.flush

theorem geometryRow091_meanGap_field :
    geometryRowsJson091.getObjVal? "mean_gap" = .ok (.str geometryRow091_meanGapText) := by rfl

theorem geometryRow091_meanGap_numerator_no_slash :
    geometryRow091_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow091_meanGap_numerator_parse :
    SourceJson.intChars geometryRow091_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow091_meanGap_denominator_parse :
    SourceJson.intChars geometryRow091_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow091_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow091_meanGap_parse :
    parseRational geometryRow091_meanGapText = .ok geometryRowsTyped091.meanGap :=
  original_rational_fraction_of_chars geometryRow091_meanGapNumeratorChars geometryRow091_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow091_meanGap_numerator_no_slash geometryRow091_meanGap_numerator_parse
    geometryRow091_meanGap_denominator_parse geometryRow091_meanGap_denominator_nonzero

theorem geometryRow091_meanGap_read :
    rationalField geometryRowsJson091 "mean_gap" = .ok geometryRowsTyped091.meanGap :=
  original_rationalField_of_string geometryRowsJson091 "mean_gap" geometryRow091_meanGapText
    geometryRowsTyped091.meanGap geometryRow091_meanGap_field geometryRow091_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_meanGap_complete"
  err.flush

noncomputable def geometryRow091_jensenBoundNumeratorChars : List Char := ['1', '1', '6', '9', '5', '6', '6', '1', '9', '8', '9', '1', '5', '3', '4', '2', '5', '1', '4', '7', '9', '0', '0', '4', '4', '2', '1', '2', '2', '4', '0', '6', '6', '8', '6', '8', '9', '7', '1', '4', '8', '0', '1', '0', '2', '2', '1', '6', '8', '5', '5', '4', '5', '3', '6', '0', '4', '2', '5', '6', '0', '1', '8', '0', '7', '0', '4', '0', '6', '4', '0', '8', '4', '6', '0', '9', '5', '9', '4', '5', '8', '8', '4', '9', '1', '7', '1', '1', '3', '7', '2', '8', '5', '0', '4', '6', '0', '3', '3', '7', '9', '9', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow091_jensenBoundDenominatorChars : List Char := ['3', '6', '8', '0', '2', '5', '9', '2', '1', '3', '6', '0', '7', '1', '3', '3', '1', '3', '1', '2', '5', '8', '0', '9', '3', '3', '3', '3', '2', '5', '7', '0', '0', '1', '2', '0', '6', '7', '7', '5', '3', '0', '3', '6', '0', '7', '6', '2', '8', '3', '2', '5', '0', '5', '9', '0', '1', '3', '7', '3', '1', '7', '2', '9', '3', '9', '5', '7', '1', '0', '6', '6', '2', '7', '4', '9', '0', '5', '5', '5', '1', '4', '3', '5', '2', '1', '8', '1', '2', '4', '6', '9', '9', '2', '0', '8', '6', '7', '7', '5', '9', '6', '4', '1', '4', '0', '0', '9', '7', '0', '3', '8', '5', '5', '3', '8', '6', '5', '9', '0', '8', '1', '0', '9', '5', '7', '8', '1', '7', '1', '4', '7', '8', '2', '5', '3', '2', '7', '3', '3', '0', '8', '0', '9']
noncomputable def geometryRow091_jensenBoundText : String := String.ofList (geometryRow091_jensenBoundNumeratorChars ++ '/' :: geometryRow091_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_jensenBound_before_field"
  err.flush

theorem geometryRow091_jensenBound_field :
    geometryRowsJson091.getObjVal? "jensen_bound" = .ok (.str geometryRow091_jensenBoundText) := by rfl

theorem geometryRow091_jensenBound_numerator_no_slash :
    geometryRow091_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow091_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow091_jensenBoundNumeratorChars = some (1169566198915342514790044212240668689714801022168554536042560180704064084609594588491711372850460337995200000000000000000000000 : Int) := by decide +kernel

theorem geometryRow091_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow091_jensenBoundDenominatorChars = some (368025921360713313125809333325700120677530360762832505901373172939571066274905551435218124699208677596414009703855386590810957817147825327330809 : Int) := by decide +kernel

theorem geometryRow091_jensenBound_denominator_nonzero : (368025921360713313125809333325700120677530360762832505901373172939571066274905551435218124699208677596414009703855386590810957817147825327330809 : Int) ≠ 0 := by decide +kernel

theorem geometryRow091_jensenBound_parse :
    parseRational geometryRow091_jensenBoundText = .ok geometryRowsTyped091.jensenBound :=
  original_rational_fraction_of_chars geometryRow091_jensenBoundNumeratorChars geometryRow091_jensenBoundDenominatorChars
    (1169566198915342514790044212240668689714801022168554536042560180704064084609594588491711372850460337995200000000000000000000000 : Int) (368025921360713313125809333325700120677530360762832505901373172939571066274905551435218124699208677596414009703855386590810957817147825327330809 : Int)
    geometryRow091_jensenBound_numerator_no_slash geometryRow091_jensenBound_numerator_parse
    geometryRow091_jensenBound_denominator_parse geometryRow091_jensenBound_denominator_nonzero

theorem geometryRow091_jensenBound_read :
    rationalField geometryRowsJson091 "jensen_bound" = .ok geometryRowsTyped091.jensenBound :=
  original_rationalField_of_string geometryRowsJson091 "jensen_bound" geometryRow091_jensenBoundText
    geometryRowsTyped091.jensenBound geometryRow091_jensenBound_field geometryRow091_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_factorMaxima_before"
  err.flush

theorem geometryRow091_factorMaxima_read :
    rationalArrayField geometryRowsJson091 "factor_maxima" = .ok geometryRowsTyped091.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_gapWeightedMeans_before"
  err.flush

theorem geometryRow091_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson091 "gap_weighted_means" = .ok geometryRowsTyped091.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow091_floorChars : List Char := ['2', '5', '1', '7', '8', '2', '7', '5', '6', '3', '2', '3']
noncomputable def geometryRow091_floorText : String := String.ofList geometryRow091_floorChars

theorem geometryRow091_floor_text_read :
    geometryRowsJson091.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow091_floorText := by rfl

theorem geometryRow091_floor_chars_parse :
    SourceJson.intChars geometryRow091_floorChars = some (251782756323 : Int) := by decide +kernel

theorem geometryRow091_floor_parse :
    parseInteger geometryRow091_floorText = .ok geometryRowsTyped091.jensenFloorQ96 := by
  simp only [geometryRow091_floorText, parseInteger, String.toList_ofList, geometryRow091_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_091 :
    decodeGeometryRow geometryRowsJson091 = .ok geometryRowsTyped091 :=
  original_geometryRow_of_fields geometryRowsJson091 geometryRowsTyped091 geometryRow091_floorText
    geometryRow091_simplexId_read geometryRow091_vertexIds_read
    geometryRow091_physicalVolume_read geometryRow091_meanGap_read
    geometryRow091_factorMaxima_read geometryRow091_gapWeightedMeans_read
    geometryRow091_jensenBound_read geometryRow091_floor_text_read geometryRow091_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_091_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson092 : SourceJson :=
  (SimplicesBlock046.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped092 : GeometryRow :=
  { simplexId := 92,
    vertexIds := #[39, 37, 24, 23, 21, 20, 16, 15, 0],
    physicalVolume := ((87364275293203199530810541525404860242513 : ℚ) / (15732671578808647680000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((70502904657277 : ℚ) / (917021700000000 : ℚ)), ((35337067696781 : ℚ) / (458510850000000 : ℚ)), ((202246698001897 : ℚ) / (1375532550000000 : ℚ)), ((96893908646077 : ℚ) / (917021700000000 : ℚ)), ((282844693087583 : ℚ) / (5502130200000000 : ℚ)), ((131434814132287 : ℚ) / (2751065100000000 : ℚ)), ((2481418853771 : ℚ) / (57917160000000 : ℚ)), ((46559366431871 : ℚ) / (1100426040000000 : ℚ)), ((114845290230833 : ℚ) / (2751065100000000 : ℚ)), ((114844556613473 : ℚ) / (2751065100000000 : ℚ))],
    jensenBound := ((8922823368833376763328794158904691633649611874102043456011232864244052732918860859656680064682760012976074218750000000000 : ℚ) / (2765697188491933767657570463339410389532516917410441096095716828173438437275590852431651608427533407101572504749833975194402405905759350097 : ℚ)),
    jensenFloorQ96 := (255609653469 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_simplexId_before"
  err.flush

theorem geometryRow092_simplexId_read :
    geometryRowsJson092.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped092.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_vertexIds_before"
  err.flush

theorem geometryRow092_vertexIds_read :
    geometryRowsJson092.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped092.vertexIds := by decide +kernel

noncomputable def geometryRow092_physicalVolumeNumeratorChars : List Char := ['8', '7', '3', '6', '4', '2', '7', '5', '2', '9', '3', '2', '0', '3', '1', '9', '9', '5', '3', '0', '8', '1', '0', '5', '4', '1', '5', '2', '5', '4', '0', '4', '8', '6', '0', '2', '4', '2', '5', '1', '3']
noncomputable def geometryRow092_physicalVolumeDenominatorChars : List Char := ['1', '5', '7', '3', '2', '6', '7', '1', '5', '7', '8', '8', '0', '8', '6', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow092_physicalVolumeText : String := String.ofList (geometryRow092_physicalVolumeNumeratorChars ++ '/' :: geometryRow092_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_physicalVolume_before_field"
  err.flush

theorem geometryRow092_physicalVolume_field :
    geometryRowsJson092.getObjVal? "physical_volume" = .ok (.str geometryRow092_physicalVolumeText) := by rfl

theorem geometryRow092_physicalVolume_numerator_no_slash :
    geometryRow092_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow092_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow092_physicalVolumeNumeratorChars = some (87364275293203199530810541525404860242513 : Int) := by decide +kernel

theorem geometryRow092_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow092_physicalVolumeDenominatorChars = some (15732671578808647680000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow092_physicalVolume_denominator_nonzero : (15732671578808647680000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow092_physicalVolume_parse :
    parseRational geometryRow092_physicalVolumeText = .ok geometryRowsTyped092.physicalVolume :=
  original_rational_fraction_of_chars geometryRow092_physicalVolumeNumeratorChars geometryRow092_physicalVolumeDenominatorChars
    (87364275293203199530810541525404860242513 : Int) (15732671578808647680000000000000000000000000000000000000000000000000 : Int)
    geometryRow092_physicalVolume_numerator_no_slash geometryRow092_physicalVolume_numerator_parse
    geometryRow092_physicalVolume_denominator_parse geometryRow092_physicalVolume_denominator_nonzero

theorem geometryRow092_physicalVolume_read :
    rationalField geometryRowsJson092 "physical_volume" = .ok geometryRowsTyped092.physicalVolume :=
  original_rationalField_of_string geometryRowsJson092 "physical_volume" geometryRow092_physicalVolumeText
    geometryRowsTyped092.physicalVolume geometryRow092_physicalVolume_field geometryRow092_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_physicalVolume_complete"
  err.flush

noncomputable def geometryRow092_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow092_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow092_meanGapText : String := String.ofList (geometryRow092_meanGapNumeratorChars ++ '/' :: geometryRow092_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_meanGap_before_field"
  err.flush

theorem geometryRow092_meanGap_field :
    geometryRowsJson092.getObjVal? "mean_gap" = .ok (.str geometryRow092_meanGapText) := by rfl

theorem geometryRow092_meanGap_numerator_no_slash :
    geometryRow092_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow092_meanGap_numerator_parse :
    SourceJson.intChars geometryRow092_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow092_meanGap_denominator_parse :
    SourceJson.intChars geometryRow092_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow092_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow092_meanGap_parse :
    parseRational geometryRow092_meanGapText = .ok geometryRowsTyped092.meanGap :=
  original_rational_fraction_of_chars geometryRow092_meanGapNumeratorChars geometryRow092_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow092_meanGap_numerator_no_slash geometryRow092_meanGap_numerator_parse
    geometryRow092_meanGap_denominator_parse geometryRow092_meanGap_denominator_nonzero

theorem geometryRow092_meanGap_read :
    rationalField geometryRowsJson092 "mean_gap" = .ok geometryRowsTyped092.meanGap :=
  original_rationalField_of_string geometryRowsJson092 "mean_gap" geometryRow092_meanGapText
    geometryRowsTyped092.meanGap geometryRow092_meanGap_field geometryRow092_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_meanGap_complete"
  err.flush

noncomputable def geometryRow092_jensenBoundNumeratorChars : List Char := ['8', '9', '2', '2', '8', '2', '3', '3', '6', '8', '8', '3', '3', '3', '7', '6', '7', '6', '3', '3', '2', '8', '7', '9', '4', '1', '5', '8', '9', '0', '4', '6', '9', '1', '6', '3', '3', '6', '4', '9', '6', '1', '1', '8', '7', '4', '1', '0', '2', '0', '4', '3', '4', '5', '6', '0', '1', '1', '2', '3', '2', '8', '6', '4', '2', '4', '4', '0', '5', '2', '7', '3', '2', '9', '1', '8', '8', '6', '0', '8', '5', '9', '6', '5', '6', '6', '8', '0', '0', '6', '4', '6', '8', '2', '7', '6', '0', '0', '1', '2', '9', '7', '6', '0', '7', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow092_jensenBoundDenominatorChars : List Char := ['2', '7', '6', '5', '6', '9', '7', '1', '8', '8', '4', '9', '1', '9', '3', '3', '7', '6', '7', '6', '5', '7', '5', '7', '0', '4', '6', '3', '3', '3', '9', '4', '1', '0', '3', '8', '9', '5', '3', '2', '5', '1', '6', '9', '1', '7', '4', '1', '0', '4', '4', '1', '0', '9', '6', '0', '9', '5', '7', '1', '6', '8', '2', '8', '1', '7', '3', '4', '3', '8', '4', '3', '7', '2', '7', '5', '5', '9', '0', '8', '5', '2', '4', '3', '1', '6', '5', '1', '6', '0', '8', '4', '2', '7', '5', '3', '3', '4', '0', '7', '1', '0', '1', '5', '7', '2', '5', '0', '4', '7', '4', '9', '8', '3', '3', '9', '7', '5', '1', '9', '4', '4', '0', '2', '4', '0', '5', '9', '0', '5', '7', '5', '9', '3', '5', '0', '0', '9', '7']
noncomputable def geometryRow092_jensenBoundText : String := String.ofList (geometryRow092_jensenBoundNumeratorChars ++ '/' :: geometryRow092_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_jensenBound_before_field"
  err.flush

theorem geometryRow092_jensenBound_field :
    geometryRowsJson092.getObjVal? "jensen_bound" = .ok (.str geometryRow092_jensenBoundText) := by rfl

theorem geometryRow092_jensenBound_numerator_no_slash :
    geometryRow092_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow092_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow092_jensenBoundNumeratorChars = some (8922823368833376763328794158904691633649611874102043456011232864244052732918860859656680064682760012976074218750000000000 : Int) := by decide +kernel

theorem geometryRow092_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow092_jensenBoundDenominatorChars = some (2765697188491933767657570463339410389532516917410441096095716828173438437275590852431651608427533407101572504749833975194402405905759350097 : Int) := by decide +kernel

theorem geometryRow092_jensenBound_denominator_nonzero : (2765697188491933767657570463339410389532516917410441096095716828173438437275590852431651608427533407101572504749833975194402405905759350097 : Int) ≠ 0 := by decide +kernel

theorem geometryRow092_jensenBound_parse :
    parseRational geometryRow092_jensenBoundText = .ok geometryRowsTyped092.jensenBound :=
  original_rational_fraction_of_chars geometryRow092_jensenBoundNumeratorChars geometryRow092_jensenBoundDenominatorChars
    (8922823368833376763328794158904691633649611874102043456011232864244052732918860859656680064682760012976074218750000000000 : Int) (2765697188491933767657570463339410389532516917410441096095716828173438437275590852431651608427533407101572504749833975194402405905759350097 : Int)
    geometryRow092_jensenBound_numerator_no_slash geometryRow092_jensenBound_numerator_parse
    geometryRow092_jensenBound_denominator_parse geometryRow092_jensenBound_denominator_nonzero

theorem geometryRow092_jensenBound_read :
    rationalField geometryRowsJson092 "jensen_bound" = .ok geometryRowsTyped092.jensenBound :=
  original_rationalField_of_string geometryRowsJson092 "jensen_bound" geometryRow092_jensenBoundText
    geometryRowsTyped092.jensenBound geometryRow092_jensenBound_field geometryRow092_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_factorMaxima_before"
  err.flush

theorem geometryRow092_factorMaxima_read :
    rationalArrayField geometryRowsJson092 "factor_maxima" = .ok geometryRowsTyped092.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_gapWeightedMeans_before"
  err.flush

theorem geometryRow092_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson092 "gap_weighted_means" = .ok geometryRowsTyped092.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow092_floorChars : List Char := ['2', '5', '5', '6', '0', '9', '6', '5', '3', '4', '6', '9']
noncomputable def geometryRow092_floorText : String := String.ofList geometryRow092_floorChars

theorem geometryRow092_floor_text_read :
    geometryRowsJson092.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow092_floorText := by rfl

theorem geometryRow092_floor_chars_parse :
    SourceJson.intChars geometryRow092_floorChars = some (255609653469 : Int) := by decide +kernel

theorem geometryRow092_floor_parse :
    parseInteger geometryRow092_floorText = .ok geometryRowsTyped092.jensenFloorQ96 := by
  simp only [geometryRow092_floorText, parseInteger, String.toList_ofList, geometryRow092_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_092 :
    decodeGeometryRow geometryRowsJson092 = .ok geometryRowsTyped092 :=
  original_geometryRow_of_fields geometryRowsJson092 geometryRowsTyped092 geometryRow092_floorText
    geometryRow092_simplexId_read geometryRow092_vertexIds_read
    geometryRow092_physicalVolume_read geometryRow092_meanGap_read
    geometryRow092_factorMaxima_read geometryRow092_gapWeightedMeans_read
    geometryRow092_jensenBound_read geometryRow092_floor_text_read geometryRow092_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_092_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock046 : List SourceJson := [geometryRowsJson091, geometryRowsJson092]
noncomputable def geometryRowsTypedBlock046 : List (GeometryRow) := [geometryRowsTyped091, geometryRowsTyped092]
noncomputable def geometryRowsTypedThroughBlock046 : List (GeometryRow) := geometryRowsTypedThroughBlock045 ++ geometryRowsTypedBlock046

theorem geometry_Rows_block_046_push_eq (acc : List SourceJson) :
    SimplicesBlock046.blockPush acc = [geometryRowsJson092, geometryRowsJson091] ++ acc := by rfl

theorem geometry_Rows_block_046_reverse (acc : List SourceJson) :
    (SimplicesBlock046.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock046 := by
  rw [geometry_Rows_block_046_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_046 :
    geometryRowsJsonBlock046.mapM decodeGeometryRow = .ok geometryRowsTypedBlock046 := by
  simp only [geometryRowsJsonBlock046, geometryRowsTypedBlock046, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_091, decode_geometry_Rows_092]
  rfl

theorem decode_geometry_Rows_through_block_046 :
    SimplicesValue.arrayAcc047.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock046 := by
  change (SimplicesBlock046.blockPush SimplicesValue.arrayAcc046).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_046_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_045, decode_geometry_Rows_block_046]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_046_complete"
  err.flush

#print axioms geometryRow091_simplexId_read
#print axioms geometryRow091_vertexIds_read
#print axioms geometryRow091_physicalVolume_field
#print axioms geometryRow091_physicalVolume_numerator_no_slash
#print axioms geometryRow091_physicalVolume_numerator_parse
#print axioms geometryRow091_physicalVolume_denominator_parse
#print axioms geometryRow091_physicalVolume_denominator_nonzero
#print axioms geometryRow091_physicalVolume_parse
#print axioms geometryRow091_physicalVolume_read
#print axioms geometryRow091_meanGap_field
#print axioms geometryRow091_meanGap_numerator_no_slash
#print axioms geometryRow091_meanGap_numerator_parse
#print axioms geometryRow091_meanGap_denominator_parse
#print axioms geometryRow091_meanGap_denominator_nonzero
#print axioms geometryRow091_meanGap_parse
#print axioms geometryRow091_meanGap_read
#print axioms geometryRow091_jensenBound_field
#print axioms geometryRow091_jensenBound_numerator_no_slash
#print axioms geometryRow091_jensenBound_numerator_parse
#print axioms geometryRow091_jensenBound_denominator_parse
#print axioms geometryRow091_jensenBound_denominator_nonzero
#print axioms geometryRow091_jensenBound_parse
#print axioms geometryRow091_jensenBound_read
#print axioms geometryRow091_factorMaxima_read
#print axioms geometryRow091_gapWeightedMeans_read
#print axioms geometryRow091_floor_text_read
#print axioms geometryRow091_floor_chars_parse
#print axioms geometryRow091_floor_parse
#print axioms decode_geometry_Rows_091
#print axioms geometryRow092_simplexId_read
#print axioms geometryRow092_vertexIds_read
#print axioms geometryRow092_physicalVolume_field
#print axioms geometryRow092_physicalVolume_numerator_no_slash
#print axioms geometryRow092_physicalVolume_numerator_parse
#print axioms geometryRow092_physicalVolume_denominator_parse
#print axioms geometryRow092_physicalVolume_denominator_nonzero
#print axioms geometryRow092_physicalVolume_parse
#print axioms geometryRow092_physicalVolume_read
#print axioms geometryRow092_meanGap_field
#print axioms geometryRow092_meanGap_numerator_no_slash
#print axioms geometryRow092_meanGap_numerator_parse
#print axioms geometryRow092_meanGap_denominator_parse
#print axioms geometryRow092_meanGap_denominator_nonzero
#print axioms geometryRow092_meanGap_parse
#print axioms geometryRow092_meanGap_read
#print axioms geometryRow092_jensenBound_field
#print axioms geometryRow092_jensenBound_numerator_no_slash
#print axioms geometryRow092_jensenBound_numerator_parse
#print axioms geometryRow092_jensenBound_denominator_parse
#print axioms geometryRow092_jensenBound_denominator_nonzero
#print axioms geometryRow092_jensenBound_parse
#print axioms geometryRow092_jensenBound_read
#print axioms geometryRow092_factorMaxima_read
#print axioms geometryRow092_gapWeightedMeans_read
#print axioms geometryRow092_floor_text_read
#print axioms geometryRow092_floor_chars_parse
#print axioms geometryRow092_floor_parse
#print axioms decode_geometry_Rows_092
#print axioms geometry_Rows_block_046_push_eq
#print axioms geometry_Rows_block_046_reverse
#print axioms decode_geometry_Rows_block_046
#print axioms decode_geometry_Rows_through_block_046

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
