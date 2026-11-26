import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows024

/-! Original simplices typed block 25, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson049 : SourceJson :=
  (SimplicesBlock025.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped049 : GeometryRow :=
  { simplexId := 49,
    vertexIds := #[39, 35, 24, 23, 21, 19, 18, 6, 0],
    physicalVolume := ((90602149153241964435173872243155248362894841 : ℚ) / (986919993937920000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((25623467964379 : ℚ) / (347555600000000 : ℚ)), ((25699582515759 : ℚ) / (347555600000000 : ℚ)), ((456796226315461 : ℚ) / (3128000400000000 : ℚ)), ((55407469622831 : ℚ) / (521333400000000 : ℚ)), ((177198125196929 : ℚ) / (3128000400000000 : ℚ)), ((149371181956967 : ℚ) / (3128000400000000 : ℚ)), ((7011421636039 : ℚ) / (164631600000000 : ℚ)), ((131546760393961 : ℚ) / (3128000400000000 : ℚ)), ((130170843267643 : ℚ) / (3128000400000000 : ℚ)), ((25145545300823 : ℚ) / (625600080000000 : ℚ))],
    jensenBound := ((2629551159779718824770091138626016462562523949481726547647762528471063646852130994306473529011969812992000000000000000000000 : ℚ) / (40357831183340568072723015803128460073503258393314236695734563338077624983954215423983936694508899891220845972404499422544562379006334851 : ℚ)),
    jensenFloorQ96 := (5162182915136402 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_simplexId_before"
  err.flush

theorem geometryRow049_simplexId_read :
    geometryRowsJson049.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped049.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_vertexIds_before"
  err.flush

theorem geometryRow049_vertexIds_read :
    geometryRowsJson049.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped049.vertexIds := by decide +kernel

noncomputable def geometryRow049_physicalVolumeNumeratorChars : List Char := ['9', '0', '6', '0', '2', '1', '4', '9', '1', '5', '3', '2', '4', '1', '9', '6', '4', '4', '3', '5', '1', '7', '3', '8', '7', '2', '2', '4', '3', '1', '5', '5', '2', '4', '8', '3', '6', '2', '8', '9', '4', '8', '4', '1']
noncomputable def geometryRow049_physicalVolumeDenominatorChars : List Char := ['9', '8', '6', '9', '1', '9', '9', '9', '3', '9', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_physicalVolumeText : String := String.ofList (geometryRow049_physicalVolumeNumeratorChars ++ '/' :: geometryRow049_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_physicalVolume_before_field"
  err.flush

theorem geometryRow049_physicalVolume_field :
    geometryRowsJson049.getObjVal? "physical_volume" = .ok (.str geometryRow049_physicalVolumeText) := by rfl

theorem geometryRow049_physicalVolume_numerator_no_slash :
    geometryRow049_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow049_physicalVolumeNumeratorChars = some (90602149153241964435173872243155248362894841 : Int) := by decide +kernel

theorem geometryRow049_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow049_physicalVolumeDenominatorChars = some (986919993937920000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow049_physicalVolume_denominator_nonzero : (986919993937920000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_physicalVolume_parse :
    parseRational geometryRow049_physicalVolumeText = .ok geometryRowsTyped049.physicalVolume :=
  original_rational_fraction_of_chars geometryRow049_physicalVolumeNumeratorChars geometryRow049_physicalVolumeDenominatorChars
    (90602149153241964435173872243155248362894841 : Int) (986919993937920000000000000000000000000000000000000000000000000000 : Int)
    geometryRow049_physicalVolume_numerator_no_slash geometryRow049_physicalVolume_numerator_parse
    geometryRow049_physicalVolume_denominator_parse geometryRow049_physicalVolume_denominator_nonzero

theorem geometryRow049_physicalVolume_read :
    rationalField geometryRowsJson049 "physical_volume" = .ok geometryRowsTyped049.physicalVolume :=
  original_rationalField_of_string geometryRowsJson049 "physical_volume" geometryRow049_physicalVolumeText
    geometryRowsTyped049.physicalVolume geometryRow049_physicalVolume_field geometryRow049_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_physicalVolume_complete"
  err.flush

noncomputable def geometryRow049_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow049_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_meanGapText : String := String.ofList (geometryRow049_meanGapNumeratorChars ++ '/' :: geometryRow049_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_meanGap_before_field"
  err.flush

theorem geometryRow049_meanGap_field :
    geometryRowsJson049.getObjVal? "mean_gap" = .ok (.str geometryRow049_meanGapText) := by rfl

theorem geometryRow049_meanGap_numerator_no_slash :
    geometryRow049_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_meanGap_numerator_parse :
    SourceJson.intChars geometryRow049_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow049_meanGap_denominator_parse :
    SourceJson.intChars geometryRow049_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow049_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_meanGap_parse :
    parseRational geometryRow049_meanGapText = .ok geometryRowsTyped049.meanGap :=
  original_rational_fraction_of_chars geometryRow049_meanGapNumeratorChars geometryRow049_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow049_meanGap_numerator_no_slash geometryRow049_meanGap_numerator_parse
    geometryRow049_meanGap_denominator_parse geometryRow049_meanGap_denominator_nonzero

theorem geometryRow049_meanGap_read :
    rationalField geometryRowsJson049 "mean_gap" = .ok geometryRowsTyped049.meanGap :=
  original_rationalField_of_string geometryRowsJson049 "mean_gap" geometryRow049_meanGapText
    geometryRowsTyped049.meanGap geometryRow049_meanGap_field geometryRow049_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_meanGap_complete"
  err.flush

noncomputable def geometryRow049_jensenBoundNumeratorChars : List Char := ['2', '6', '2', '9', '5', '5', '1', '1', '5', '9', '7', '7', '9', '7', '1', '8', '8', '2', '4', '7', '7', '0', '0', '9', '1', '1', '3', '8', '6', '2', '6', '0', '1', '6', '4', '6', '2', '5', '6', '2', '5', '2', '3', '9', '4', '9', '4', '8', '1', '7', '2', '6', '5', '4', '7', '6', '4', '7', '7', '6', '2', '5', '2', '8', '4', '7', '1', '0', '6', '3', '6', '4', '6', '8', '5', '2', '1', '3', '0', '9', '9', '4', '3', '0', '6', '4', '7', '3', '5', '2', '9', '0', '1', '1', '9', '6', '9', '8', '1', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_jensenBoundDenominatorChars : List Char := ['4', '0', '3', '5', '7', '8', '3', '1', '1', '8', '3', '3', '4', '0', '5', '6', '8', '0', '7', '2', '7', '2', '3', '0', '1', '5', '8', '0', '3', '1', '2', '8', '4', '6', '0', '0', '7', '3', '5', '0', '3', '2', '5', '8', '3', '9', '3', '3', '1', '4', '2', '3', '6', '6', '9', '5', '7', '3', '4', '5', '6', '3', '3', '3', '8', '0', '7', '7', '6', '2', '4', '9', '8', '3', '9', '5', '4', '2', '1', '5', '4', '2', '3', '9', '8', '3', '9', '3', '6', '6', '9', '4', '5', '0', '8', '8', '9', '9', '8', '9', '1', '2', '2', '0', '8', '4', '5', '9', '7', '2', '4', '0', '4', '4', '9', '9', '4', '2', '2', '5', '4', '4', '5', '6', '2', '3', '7', '9', '0', '0', '6', '3', '3', '4', '8', '5', '1']
noncomputable def geometryRow049_jensenBoundText : String := String.ofList (geometryRow049_jensenBoundNumeratorChars ++ '/' :: geometryRow049_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_jensenBound_before_field"
  err.flush

theorem geometryRow049_jensenBound_field :
    geometryRowsJson049.getObjVal? "jensen_bound" = .ok (.str geometryRow049_jensenBoundText) := by rfl

theorem geometryRow049_jensenBound_numerator_no_slash :
    geometryRow049_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow049_jensenBoundNumeratorChars = some (2629551159779718824770091138626016462562523949481726547647762528471063646852130994306473529011969812992000000000000000000000 : Int) := by decide +kernel

theorem geometryRow049_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow049_jensenBoundDenominatorChars = some (40357831183340568072723015803128460073503258393314236695734563338077624983954215423983936694508899891220845972404499422544562379006334851 : Int) := by decide +kernel

theorem geometryRow049_jensenBound_denominator_nonzero : (40357831183340568072723015803128460073503258393314236695734563338077624983954215423983936694508899891220845972404499422544562379006334851 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_jensenBound_parse :
    parseRational geometryRow049_jensenBoundText = .ok geometryRowsTyped049.jensenBound :=
  original_rational_fraction_of_chars geometryRow049_jensenBoundNumeratorChars geometryRow049_jensenBoundDenominatorChars
    (2629551159779718824770091138626016462562523949481726547647762528471063646852130994306473529011969812992000000000000000000000 : Int) (40357831183340568072723015803128460073503258393314236695734563338077624983954215423983936694508899891220845972404499422544562379006334851 : Int)
    geometryRow049_jensenBound_numerator_no_slash geometryRow049_jensenBound_numerator_parse
    geometryRow049_jensenBound_denominator_parse geometryRow049_jensenBound_denominator_nonzero

theorem geometryRow049_jensenBound_read :
    rationalField geometryRowsJson049 "jensen_bound" = .ok geometryRowsTyped049.jensenBound :=
  original_rationalField_of_string geometryRowsJson049 "jensen_bound" geometryRow049_jensenBoundText
    geometryRowsTyped049.jensenBound geometryRow049_jensenBound_field geometryRow049_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_factorMaxima_before"
  err.flush

theorem geometryRow049_factorMaxima_read :
    rationalArrayField geometryRowsJson049 "factor_maxima" = .ok geometryRowsTyped049.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_gapWeightedMeans_before"
  err.flush

theorem geometryRow049_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson049 "gap_weighted_means" = .ok geometryRowsTyped049.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow049_floorChars : List Char := ['5', '1', '6', '2', '1', '8', '2', '9', '1', '5', '1', '3', '6', '4', '0', '2']
noncomputable def geometryRow049_floorText : String := String.ofList geometryRow049_floorChars

theorem geometryRow049_floor_text_read :
    geometryRowsJson049.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow049_floorText := by rfl

theorem geometryRow049_floor_chars_parse :
    SourceJson.intChars geometryRow049_floorChars = some (5162182915136402 : Int) := by decide +kernel

theorem geometryRow049_floor_parse :
    parseInteger geometryRow049_floorText = .ok geometryRowsTyped049.jensenFloorQ96 := by
  simp only [geometryRow049_floorText, parseInteger, String.toList_ofList, geometryRow049_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_049 :
    decodeGeometryRow geometryRowsJson049 = .ok geometryRowsTyped049 :=
  original_geometryRow_of_fields geometryRowsJson049 geometryRowsTyped049 geometryRow049_floorText
    geometryRow049_simplexId_read geometryRow049_vertexIds_read
    geometryRow049_physicalVolume_read geometryRow049_meanGap_read
    geometryRow049_factorMaxima_read geometryRow049_gapWeightedMeans_read
    geometryRow049_jensenBound_read geometryRow049_floor_text_read geometryRow049_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_049_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson050 : SourceJson :=
  (SimplicesBlock025.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped050 : GeometryRow :=
  { simplexId := 50,
    vertexIds := #[39, 35, 24, 23, 21, 19, 18, 15, 0],
    physicalVolume := ((31676428690578580885160725474605996530282021 : ℚ) / (1015117708050432000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((44846676343687 : ℚ) / (625600080000000 : ℚ)), ((44983682536171 : ℚ) / (625600080000000 : ℚ)), ((55009228454191 : ℚ) / (375360048000000 : ℚ)), ((13707886385153 : ℚ) / (130333350000000 : ℚ)), ((524448646853519 : ℚ) / (9384001200000000 : ℚ)), ((450182602449137 : ℚ) / (9384001200000000 : ℚ)), ((21349732306687 : ℚ) / (493894800000000 : ℚ)), ((400634161754713 : ℚ) / (9384001200000000 : ℚ)), ((396506410375759 : ℚ) / (9384001200000000 : ℚ)), ((392391845400679 : ℚ) / (9384001200000000 : ℚ))],
    jensenBound := ((950013841351544760036012841942539956655841694855182104286943845728175899713965177853917916890884170250627840000000000000000000 : ℚ) / (43451113280576276832045925235447492016950298883353934603808994804294923141645633381219919866724441847380984062395586296401719450121142800553 : ℚ)),
    jensenFloorQ96 := (1732242175876476 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_simplexId_before"
  err.flush

theorem geometryRow050_simplexId_read :
    geometryRowsJson050.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped050.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_vertexIds_before"
  err.flush

theorem geometryRow050_vertexIds_read :
    geometryRowsJson050.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped050.vertexIds := by decide +kernel

noncomputable def geometryRow050_physicalVolumeNumeratorChars : List Char := ['3', '1', '6', '7', '6', '4', '2', '8', '6', '9', '0', '5', '7', '8', '5', '8', '0', '8', '8', '5', '1', '6', '0', '7', '2', '5', '4', '7', '4', '6', '0', '5', '9', '9', '6', '5', '3', '0', '2', '8', '2', '0', '2', '1']
noncomputable def geometryRow050_physicalVolumeDenominatorChars : List Char := ['1', '0', '1', '5', '1', '1', '7', '7', '0', '8', '0', '5', '0', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_physicalVolumeText : String := String.ofList (geometryRow050_physicalVolumeNumeratorChars ++ '/' :: geometryRow050_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_physicalVolume_before_field"
  err.flush

theorem geometryRow050_physicalVolume_field :
    geometryRowsJson050.getObjVal? "physical_volume" = .ok (.str geometryRow050_physicalVolumeText) := by rfl

theorem geometryRow050_physicalVolume_numerator_no_slash :
    geometryRow050_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow050_physicalVolumeNumeratorChars = some (31676428690578580885160725474605996530282021 : Int) := by decide +kernel

theorem geometryRow050_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow050_physicalVolumeDenominatorChars = some (1015117708050432000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow050_physicalVolume_denominator_nonzero : (1015117708050432000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_physicalVolume_parse :
    parseRational geometryRow050_physicalVolumeText = .ok geometryRowsTyped050.physicalVolume :=
  original_rational_fraction_of_chars geometryRow050_physicalVolumeNumeratorChars geometryRow050_physicalVolumeDenominatorChars
    (31676428690578580885160725474605996530282021 : Int) (1015117708050432000000000000000000000000000000000000000000000000000 : Int)
    geometryRow050_physicalVolume_numerator_no_slash geometryRow050_physicalVolume_numerator_parse
    geometryRow050_physicalVolume_denominator_parse geometryRow050_physicalVolume_denominator_nonzero

theorem geometryRow050_physicalVolume_read :
    rationalField geometryRowsJson050 "physical_volume" = .ok geometryRowsTyped050.physicalVolume :=
  original_rationalField_of_string geometryRowsJson050 "physical_volume" geometryRow050_physicalVolumeText
    geometryRowsTyped050.physicalVolume geometryRow050_physicalVolume_field geometryRow050_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_physicalVolume_complete"
  err.flush

noncomputable def geometryRow050_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow050_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_meanGapText : String := String.ofList (geometryRow050_meanGapNumeratorChars ++ '/' :: geometryRow050_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_meanGap_before_field"
  err.flush

theorem geometryRow050_meanGap_field :
    geometryRowsJson050.getObjVal? "mean_gap" = .ok (.str geometryRow050_meanGapText) := by rfl

theorem geometryRow050_meanGap_numerator_no_slash :
    geometryRow050_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_meanGap_numerator_parse :
    SourceJson.intChars geometryRow050_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow050_meanGap_denominator_parse :
    SourceJson.intChars geometryRow050_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow050_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_meanGap_parse :
    parseRational geometryRow050_meanGapText = .ok geometryRowsTyped050.meanGap :=
  original_rational_fraction_of_chars geometryRow050_meanGapNumeratorChars geometryRow050_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow050_meanGap_numerator_no_slash geometryRow050_meanGap_numerator_parse
    geometryRow050_meanGap_denominator_parse geometryRow050_meanGap_denominator_nonzero

theorem geometryRow050_meanGap_read :
    rationalField geometryRowsJson050 "mean_gap" = .ok geometryRowsTyped050.meanGap :=
  original_rationalField_of_string geometryRowsJson050 "mean_gap" geometryRow050_meanGapText
    geometryRowsTyped050.meanGap geometryRow050_meanGap_field geometryRow050_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_meanGap_complete"
  err.flush

noncomputable def geometryRow050_jensenBoundNumeratorChars : List Char := ['9', '5', '0', '0', '1', '3', '8', '4', '1', '3', '5', '1', '5', '4', '4', '7', '6', '0', '0', '3', '6', '0', '1', '2', '8', '4', '1', '9', '4', '2', '5', '3', '9', '9', '5', '6', '6', '5', '5', '8', '4', '1', '6', '9', '4', '8', '5', '5', '1', '8', '2', '1', '0', '4', '2', '8', '6', '9', '4', '3', '8', '4', '5', '7', '2', '8', '1', '7', '5', '8', '9', '9', '7', '1', '3', '9', '6', '5', '1', '7', '7', '8', '5', '3', '9', '1', '7', '9', '1', '6', '8', '9', '0', '8', '8', '4', '1', '7', '0', '2', '5', '0', '6', '2', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_jensenBoundDenominatorChars : List Char := ['4', '3', '4', '5', '1', '1', '1', '3', '2', '8', '0', '5', '7', '6', '2', '7', '6', '8', '3', '2', '0', '4', '5', '9', '2', '5', '2', '3', '5', '4', '4', '7', '4', '9', '2', '0', '1', '6', '9', '5', '0', '2', '9', '8', '8', '8', '3', '3', '5', '3', '9', '3', '4', '6', '0', '3', '8', '0', '8', '9', '9', '4', '8', '0', '4', '2', '9', '4', '9', '2', '3', '1', '4', '1', '6', '4', '5', '6', '3', '3', '3', '8', '1', '2', '1', '9', '9', '1', '9', '8', '6', '6', '7', '2', '4', '4', '4', '1', '8', '4', '7', '3', '8', '0', '9', '8', '4', '0', '6', '2', '3', '9', '5', '5', '8', '6', '2', '9', '6', '4', '0', '1', '7', '1', '9', '4', '5', '0', '1', '2', '1', '1', '4', '2', '8', '0', '0', '5', '5', '3']
noncomputable def geometryRow050_jensenBoundText : String := String.ofList (geometryRow050_jensenBoundNumeratorChars ++ '/' :: geometryRow050_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_jensenBound_before_field"
  err.flush

theorem geometryRow050_jensenBound_field :
    geometryRowsJson050.getObjVal? "jensen_bound" = .ok (.str geometryRow050_jensenBoundText) := by rfl

theorem geometryRow050_jensenBound_numerator_no_slash :
    geometryRow050_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow050_jensenBoundNumeratorChars = some (950013841351544760036012841942539956655841694855182104286943845728175899713965177853917916890884170250627840000000000000000000 : Int) := by decide +kernel

theorem geometryRow050_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow050_jensenBoundDenominatorChars = some (43451113280576276832045925235447492016950298883353934603808994804294923141645633381219919866724441847380984062395586296401719450121142800553 : Int) := by decide +kernel

theorem geometryRow050_jensenBound_denominator_nonzero : (43451113280576276832045925235447492016950298883353934603808994804294923141645633381219919866724441847380984062395586296401719450121142800553 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_jensenBound_parse :
    parseRational geometryRow050_jensenBoundText = .ok geometryRowsTyped050.jensenBound :=
  original_rational_fraction_of_chars geometryRow050_jensenBoundNumeratorChars geometryRow050_jensenBoundDenominatorChars
    (950013841351544760036012841942539956655841694855182104286943845728175899713965177853917916890884170250627840000000000000000000 : Int) (43451113280576276832045925235447492016950298883353934603808994804294923141645633381219919866724441847380984062395586296401719450121142800553 : Int)
    geometryRow050_jensenBound_numerator_no_slash geometryRow050_jensenBound_numerator_parse
    geometryRow050_jensenBound_denominator_parse geometryRow050_jensenBound_denominator_nonzero

theorem geometryRow050_jensenBound_read :
    rationalField geometryRowsJson050 "jensen_bound" = .ok geometryRowsTyped050.jensenBound :=
  original_rationalField_of_string geometryRowsJson050 "jensen_bound" geometryRow050_jensenBoundText
    geometryRowsTyped050.jensenBound geometryRow050_jensenBound_field geometryRow050_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_factorMaxima_before"
  err.flush

theorem geometryRow050_factorMaxima_read :
    rationalArrayField geometryRowsJson050 "factor_maxima" = .ok geometryRowsTyped050.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_gapWeightedMeans_before"
  err.flush

theorem geometryRow050_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson050 "gap_weighted_means" = .ok geometryRowsTyped050.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow050_floorChars : List Char := ['1', '7', '3', '2', '2', '4', '2', '1', '7', '5', '8', '7', '6', '4', '7', '6']
noncomputable def geometryRow050_floorText : String := String.ofList geometryRow050_floorChars

theorem geometryRow050_floor_text_read :
    geometryRowsJson050.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow050_floorText := by rfl

theorem geometryRow050_floor_chars_parse :
    SourceJson.intChars geometryRow050_floorChars = some (1732242175876476 : Int) := by decide +kernel

theorem geometryRow050_floor_parse :
    parseInteger geometryRow050_floorText = .ok geometryRowsTyped050.jensenFloorQ96 := by
  simp only [geometryRow050_floorText, parseInteger, String.toList_ofList, geometryRow050_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_050 :
    decodeGeometryRow geometryRowsJson050 = .ok geometryRowsTyped050 :=
  original_geometryRow_of_fields geometryRowsJson050 geometryRowsTyped050 geometryRow050_floorText
    geometryRow050_simplexId_read geometryRow050_vertexIds_read
    geometryRow050_physicalVolume_read geometryRow050_meanGap_read
    geometryRow050_factorMaxima_read geometryRow050_gapWeightedMeans_read
    geometryRow050_jensenBound_read geometryRow050_floor_text_read geometryRow050_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_050_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock025 : List SourceJson := [geometryRowsJson049, geometryRowsJson050]
noncomputable def geometryRowsTypedBlock025 : List (GeometryRow) := [geometryRowsTyped049, geometryRowsTyped050]
noncomputable def geometryRowsTypedThroughBlock025 : List (GeometryRow) := geometryRowsTypedThroughBlock024 ++ geometryRowsTypedBlock025

theorem geometry_Rows_block_025_push_eq (acc : List SourceJson) :
    SimplicesBlock025.blockPush acc = [geometryRowsJson050, geometryRowsJson049] ++ acc := by rfl

theorem geometry_Rows_block_025_reverse (acc : List SourceJson) :
    (SimplicesBlock025.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock025 := by
  rw [geometry_Rows_block_025_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_025 :
    geometryRowsJsonBlock025.mapM decodeGeometryRow = .ok geometryRowsTypedBlock025 := by
  simp only [geometryRowsJsonBlock025, geometryRowsTypedBlock025, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_049, decode_geometry_Rows_050]
  rfl

theorem decode_geometry_Rows_through_block_025 :
    SimplicesValue.arrayAcc026.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock025 := by
  change (SimplicesBlock025.blockPush SimplicesValue.arrayAcc025).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_025_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_024, decode_geometry_Rows_block_025]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_025_complete"
  err.flush

#print axioms geometryRow049_simplexId_read
#print axioms geometryRow049_vertexIds_read
#print axioms geometryRow049_physicalVolume_field
#print axioms geometryRow049_physicalVolume_numerator_no_slash
#print axioms geometryRow049_physicalVolume_numerator_parse
#print axioms geometryRow049_physicalVolume_denominator_parse
#print axioms geometryRow049_physicalVolume_denominator_nonzero
#print axioms geometryRow049_physicalVolume_parse
#print axioms geometryRow049_physicalVolume_read
#print axioms geometryRow049_meanGap_field
#print axioms geometryRow049_meanGap_numerator_no_slash
#print axioms geometryRow049_meanGap_numerator_parse
#print axioms geometryRow049_meanGap_denominator_parse
#print axioms geometryRow049_meanGap_denominator_nonzero
#print axioms geometryRow049_meanGap_parse
#print axioms geometryRow049_meanGap_read
#print axioms geometryRow049_jensenBound_field
#print axioms geometryRow049_jensenBound_numerator_no_slash
#print axioms geometryRow049_jensenBound_numerator_parse
#print axioms geometryRow049_jensenBound_denominator_parse
#print axioms geometryRow049_jensenBound_denominator_nonzero
#print axioms geometryRow049_jensenBound_parse
#print axioms geometryRow049_jensenBound_read
#print axioms geometryRow049_factorMaxima_read
#print axioms geometryRow049_gapWeightedMeans_read
#print axioms geometryRow049_floor_text_read
#print axioms geometryRow049_floor_chars_parse
#print axioms geometryRow049_floor_parse
#print axioms decode_geometry_Rows_049
#print axioms geometryRow050_simplexId_read
#print axioms geometryRow050_vertexIds_read
#print axioms geometryRow050_physicalVolume_field
#print axioms geometryRow050_physicalVolume_numerator_no_slash
#print axioms geometryRow050_physicalVolume_numerator_parse
#print axioms geometryRow050_physicalVolume_denominator_parse
#print axioms geometryRow050_physicalVolume_denominator_nonzero
#print axioms geometryRow050_physicalVolume_parse
#print axioms geometryRow050_physicalVolume_read
#print axioms geometryRow050_meanGap_field
#print axioms geometryRow050_meanGap_numerator_no_slash
#print axioms geometryRow050_meanGap_numerator_parse
#print axioms geometryRow050_meanGap_denominator_parse
#print axioms geometryRow050_meanGap_denominator_nonzero
#print axioms geometryRow050_meanGap_parse
#print axioms geometryRow050_meanGap_read
#print axioms geometryRow050_jensenBound_field
#print axioms geometryRow050_jensenBound_numerator_no_slash
#print axioms geometryRow050_jensenBound_numerator_parse
#print axioms geometryRow050_jensenBound_denominator_parse
#print axioms geometryRow050_jensenBound_denominator_nonzero
#print axioms geometryRow050_jensenBound_parse
#print axioms geometryRow050_jensenBound_read
#print axioms geometryRow050_factorMaxima_read
#print axioms geometryRow050_gapWeightedMeans_read
#print axioms geometryRow050_floor_text_read
#print axioms geometryRow050_floor_chars_parse
#print axioms geometryRow050_floor_parse
#print axioms decode_geometry_Rows_050
#print axioms geometry_Rows_block_025_push_eq
#print axioms geometry_Rows_block_025_reverse
#print axioms decode_geometry_Rows_block_025
#print axioms decode_geometry_Rows_through_block_025

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
