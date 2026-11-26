import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows009

/-! Original simplices typed block 10, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson020 : SourceJson :=
  (SimplicesBlock010.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped020 : GeometryRow :=
  { simplexId := 20,
    vertexIds := #[39, 35, 29, 11, 10, 8, 3, 1, 0],
    physicalVolume := ((2692663812653007950767918131824229 : ℚ) / (1158676480000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((1323129369383 : ℚ) / (14851200000000 : ℚ)), ((1338141573863 : ℚ) / (14851200000000 : ℚ)), ((244243375801 : ℚ) / (1713600000000 : ℚ)), ((1667915133169 : ℚ) / (14851200000000 : ℚ)), ((165630797789 : ℚ) / (2620800000000 : ℚ)), ((1115968939307 : ℚ) / (22276800000000 : ℚ)), ((881281480987 : ℚ) / (22276800000000 : ℚ)), ((1560748821719 : ℚ) / (44553600000000 : ℚ)), ((1436753616119 : ℚ) / (44553600000000 : ℚ)), ((1436744705399 : ℚ) / (44553600000000 : ℚ))],
    jensenBound := ((3370329354792535809897130611336833456412675639186083940603639235684342943616860160000000000000000000000000 : ℚ) / (378533117170944828281495445602064389816085449448684096557998741936855926503627893121046682912924245931349985082228482539 : ℚ)),
    jensenFloorQ96 := (705420449982744 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_simplexId_before"
  err.flush

theorem geometryRow020_simplexId_read :
    geometryRowsJson020.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped020.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_vertexIds_before"
  err.flush

theorem geometryRow020_vertexIds_read :
    geometryRowsJson020.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped020.vertexIds := by decide +kernel

noncomputable def geometryRow020_physicalVolumeNumeratorChars : List Char := ['2', '6', '9', '2', '6', '6', '3', '8', '1', '2', '6', '5', '3', '0', '0', '7', '9', '5', '0', '7', '6', '7', '9', '1', '8', '1', '3', '1', '8', '2', '4', '2', '2', '9']
noncomputable def geometryRow020_physicalVolumeDenominatorChars : List Char := ['1', '1', '5', '8', '6', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_physicalVolumeText : String := String.ofList (geometryRow020_physicalVolumeNumeratorChars ++ '/' :: geometryRow020_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_physicalVolume_before_field"
  err.flush

theorem geometryRow020_physicalVolume_field :
    geometryRowsJson020.getObjVal? "physical_volume" = .ok (.str geometryRow020_physicalVolumeText) := by rfl

theorem geometryRow020_physicalVolume_numerator_no_slash :
    geometryRow020_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow020_physicalVolumeNumeratorChars = some (2692663812653007950767918131824229 : Int) := by decide +kernel

theorem geometryRow020_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow020_physicalVolumeDenominatorChars = some (1158676480000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow020_physicalVolume_denominator_nonzero : (1158676480000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_physicalVolume_parse :
    parseRational geometryRow020_physicalVolumeText = .ok geometryRowsTyped020.physicalVolume :=
  original_rational_fraction_of_chars geometryRow020_physicalVolumeNumeratorChars geometryRow020_physicalVolumeDenominatorChars
    (2692663812653007950767918131824229 : Int) (1158676480000000000000000000000000000000000000000000000000 : Int)
    geometryRow020_physicalVolume_numerator_no_slash geometryRow020_physicalVolume_numerator_parse
    geometryRow020_physicalVolume_denominator_parse geometryRow020_physicalVolume_denominator_nonzero

theorem geometryRow020_physicalVolume_read :
    rationalField geometryRowsJson020 "physical_volume" = .ok geometryRowsTyped020.physicalVolume :=
  original_rationalField_of_string geometryRowsJson020 "physical_volume" geometryRow020_physicalVolumeText
    geometryRowsTyped020.physicalVolume geometryRow020_physicalVolume_field geometryRow020_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_physicalVolume_complete"
  err.flush

noncomputable def geometryRow020_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow020_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_meanGapText : String := String.ofList (geometryRow020_meanGapNumeratorChars ++ '/' :: geometryRow020_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_meanGap_before_field"
  err.flush

theorem geometryRow020_meanGap_field :
    geometryRowsJson020.getObjVal? "mean_gap" = .ok (.str geometryRow020_meanGapText) := by rfl

theorem geometryRow020_meanGap_numerator_no_slash :
    geometryRow020_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_meanGap_numerator_parse :
    SourceJson.intChars geometryRow020_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow020_meanGap_denominator_parse :
    SourceJson.intChars geometryRow020_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow020_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_meanGap_parse :
    parseRational geometryRow020_meanGapText = .ok geometryRowsTyped020.meanGap :=
  original_rational_fraction_of_chars geometryRow020_meanGapNumeratorChars geometryRow020_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow020_meanGap_numerator_no_slash geometryRow020_meanGap_numerator_parse
    geometryRow020_meanGap_denominator_parse geometryRow020_meanGap_denominator_nonzero

theorem geometryRow020_meanGap_read :
    rationalField geometryRowsJson020 "mean_gap" = .ok geometryRowsTyped020.meanGap :=
  original_rationalField_of_string geometryRowsJson020 "mean_gap" geometryRow020_meanGapText
    geometryRowsTyped020.meanGap geometryRow020_meanGap_field geometryRow020_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_meanGap_complete"
  err.flush

noncomputable def geometryRow020_jensenBoundNumeratorChars : List Char := ['3', '3', '7', '0', '3', '2', '9', '3', '5', '4', '7', '9', '2', '5', '3', '5', '8', '0', '9', '8', '9', '7', '1', '3', '0', '6', '1', '1', '3', '3', '6', '8', '3', '3', '4', '5', '6', '4', '1', '2', '6', '7', '5', '6', '3', '9', '1', '8', '6', '0', '8', '3', '9', '4', '0', '6', '0', '3', '6', '3', '9', '2', '3', '5', '6', '8', '4', '3', '4', '2', '9', '4', '3', '6', '1', '6', '8', '6', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_jensenBoundDenominatorChars : List Char := ['3', '7', '8', '5', '3', '3', '1', '1', '7', '1', '7', '0', '9', '4', '4', '8', '2', '8', '2', '8', '1', '4', '9', '5', '4', '4', '5', '6', '0', '2', '0', '6', '4', '3', '8', '9', '8', '1', '6', '0', '8', '5', '4', '4', '9', '4', '4', '8', '6', '8', '4', '0', '9', '6', '5', '5', '7', '9', '9', '8', '7', '4', '1', '9', '3', '6', '8', '5', '5', '9', '2', '6', '5', '0', '3', '6', '2', '7', '8', '9', '3', '1', '2', '1', '0', '4', '6', '6', '8', '2', '9', '1', '2', '9', '2', '4', '2', '4', '5', '9', '3', '1', '3', '4', '9', '9', '8', '5', '0', '8', '2', '2', '2', '8', '4', '8', '2', '5', '3', '9']
noncomputable def geometryRow020_jensenBoundText : String := String.ofList (geometryRow020_jensenBoundNumeratorChars ++ '/' :: geometryRow020_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_jensenBound_before_field"
  err.flush

theorem geometryRow020_jensenBound_field :
    geometryRowsJson020.getObjVal? "jensen_bound" = .ok (.str geometryRow020_jensenBoundText) := by rfl

theorem geometryRow020_jensenBound_numerator_no_slash :
    geometryRow020_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow020_jensenBoundNumeratorChars = some (3370329354792535809897130611336833456412675639186083940603639235684342943616860160000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow020_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow020_jensenBoundDenominatorChars = some (378533117170944828281495445602064389816085449448684096557998741936855926503627893121046682912924245931349985082228482539 : Int) := by decide +kernel

theorem geometryRow020_jensenBound_denominator_nonzero : (378533117170944828281495445602064389816085449448684096557998741936855926503627893121046682912924245931349985082228482539 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_jensenBound_parse :
    parseRational geometryRow020_jensenBoundText = .ok geometryRowsTyped020.jensenBound :=
  original_rational_fraction_of_chars geometryRow020_jensenBoundNumeratorChars geometryRow020_jensenBoundDenominatorChars
    (3370329354792535809897130611336833456412675639186083940603639235684342943616860160000000000000000000000000 : Int) (378533117170944828281495445602064389816085449448684096557998741936855926503627893121046682912924245931349985082228482539 : Int)
    geometryRow020_jensenBound_numerator_no_slash geometryRow020_jensenBound_numerator_parse
    geometryRow020_jensenBound_denominator_parse geometryRow020_jensenBound_denominator_nonzero

theorem geometryRow020_jensenBound_read :
    rationalField geometryRowsJson020 "jensen_bound" = .ok geometryRowsTyped020.jensenBound :=
  original_rationalField_of_string geometryRowsJson020 "jensen_bound" geometryRow020_jensenBoundText
    geometryRowsTyped020.jensenBound geometryRow020_jensenBound_field geometryRow020_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_factorMaxima_before"
  err.flush

theorem geometryRow020_factorMaxima_read :
    rationalArrayField geometryRowsJson020 "factor_maxima" = .ok geometryRowsTyped020.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_gapWeightedMeans_before"
  err.flush

theorem geometryRow020_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson020 "gap_weighted_means" = .ok geometryRowsTyped020.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow020_floorChars : List Char := ['7', '0', '5', '4', '2', '0', '4', '4', '9', '9', '8', '2', '7', '4', '4']
noncomputable def geometryRow020_floorText : String := String.ofList geometryRow020_floorChars

theorem geometryRow020_floor_text_read :
    geometryRowsJson020.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow020_floorText := by rfl

theorem geometryRow020_floor_chars_parse :
    SourceJson.intChars geometryRow020_floorChars = some (705420449982744 : Int) := by decide +kernel

theorem geometryRow020_floor_parse :
    parseInteger geometryRow020_floorText = .ok geometryRowsTyped020.jensenFloorQ96 := by
  simp only [geometryRow020_floorText, parseInteger, String.toList_ofList, geometryRow020_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_020 :
    decodeGeometryRow geometryRowsJson020 = .ok geometryRowsTyped020 :=
  original_geometryRow_of_fields geometryRowsJson020 geometryRowsTyped020 geometryRow020_floorText
    geometryRow020_simplexId_read geometryRow020_vertexIds_read
    geometryRow020_physicalVolume_read geometryRow020_meanGap_read
    geometryRow020_factorMaxima_read geometryRow020_gapWeightedMeans_read
    geometryRow020_jensenBound_read geometryRow020_floor_text_read geometryRow020_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_020_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson021 : SourceJson :=
  (SimplicesBlock010.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped021 : GeometryRow :=
  { simplexId := 21,
    vertexIds := #[39, 35, 29, 11, 10, 8, 3, 2, 0],
    physicalVolume := ((28335340962619631674798454452033413127 : ℚ) / (2317352960000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1074023 : ℚ) / (937125000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((199961399169581737 : ℚ) / (2278647196800000000 : ℚ)), ((9970883566420208773 : ℚ) / (111653712643200000000 : ℚ)), ((919866132072330403 : ℚ) / (6441560344800000000 : ℚ)), ((12719387016096409349 : ℚ) / (111653712643200000000 : ℚ)), ((1246978380207326899 : ℚ) / (19703596348800000000 : ℚ)), ((4082587752076861151 : ℚ) / (83740284482400000000 : ℚ)), ((3320393391953119351 : ℚ) / (83740284482400000000 : ℚ)), ((11764302369298806349 : ℚ) / (334961137929600000000 : ℚ)), ((10889681115500068729 : ℚ) / (334961137929600000000 : ℚ)), ((10712197784412034069 : ℚ) / (334961137929600000000 : ℚ))],
    jensenBound := ((53262855523160876460971392037135914714887881073928945614380683073595722684543712604702278229477061653295644458023347548465929949920800812158784771194880000000000000000000000000 : ℚ) / (541146108105508713951452370223312080377918106400247118768568513302864722061114634422113944041192308829447712312010275258554434437522012910157208366757005999131269271944111306512093129897 : ℚ)),
    jensenFloorQ96 := (7798112395442014296 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_simplexId_before"
  err.flush

theorem geometryRow021_simplexId_read :
    geometryRowsJson021.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped021.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_vertexIds_before"
  err.flush

theorem geometryRow021_vertexIds_read :
    geometryRowsJson021.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped021.vertexIds := by decide +kernel

noncomputable def geometryRow021_physicalVolumeNumeratorChars : List Char := ['2', '8', '3', '3', '5', '3', '4', '0', '9', '6', '2', '6', '1', '9', '6', '3', '1', '6', '7', '4', '7', '9', '8', '4', '5', '4', '4', '5', '2', '0', '3', '3', '4', '1', '3', '1', '2', '7']
noncomputable def geometryRow021_physicalVolumeDenominatorChars : List Char := ['2', '3', '1', '7', '3', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow021_physicalVolumeText : String := String.ofList (geometryRow021_physicalVolumeNumeratorChars ++ '/' :: geometryRow021_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_physicalVolume_before_field"
  err.flush

theorem geometryRow021_physicalVolume_field :
    geometryRowsJson021.getObjVal? "physical_volume" = .ok (.str geometryRow021_physicalVolumeText) := by rfl

theorem geometryRow021_physicalVolume_numerator_no_slash :
    geometryRow021_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow021_physicalVolumeNumeratorChars = some (28335340962619631674798454452033413127 : Int) := by decide +kernel

theorem geometryRow021_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow021_physicalVolumeDenominatorChars = some (2317352960000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow021_physicalVolume_denominator_nonzero : (2317352960000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_physicalVolume_parse :
    parseRational geometryRow021_physicalVolumeText = .ok geometryRowsTyped021.physicalVolume :=
  original_rational_fraction_of_chars geometryRow021_physicalVolumeNumeratorChars geometryRow021_physicalVolumeDenominatorChars
    (28335340962619631674798454452033413127 : Int) (2317352960000000000000000000000000000000000000000000000000 : Int)
    geometryRow021_physicalVolume_numerator_no_slash geometryRow021_physicalVolume_numerator_parse
    geometryRow021_physicalVolume_denominator_parse geometryRow021_physicalVolume_denominator_nonzero

theorem geometryRow021_physicalVolume_read :
    rationalField geometryRowsJson021 "physical_volume" = .ok geometryRowsTyped021.physicalVolume :=
  original_rationalField_of_string geometryRowsJson021 "physical_volume" geometryRow021_physicalVolumeText
    geometryRowsTyped021.physicalVolume geometryRow021_physicalVolume_field geometryRow021_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_physicalVolume_complete"
  err.flush

noncomputable def geometryRow021_meanGapNumeratorChars : List Char := ['1', '0', '7', '4', '0', '2', '3']
noncomputable def geometryRow021_meanGapDenominatorChars : List Char := ['9', '3', '7', '1', '2', '5', '0', '0', '0']
noncomputable def geometryRow021_meanGapText : String := String.ofList (geometryRow021_meanGapNumeratorChars ++ '/' :: geometryRow021_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_meanGap_before_field"
  err.flush

theorem geometryRow021_meanGap_field :
    geometryRowsJson021.getObjVal? "mean_gap" = .ok (.str geometryRow021_meanGapText) := by rfl

theorem geometryRow021_meanGap_numerator_no_slash :
    geometryRow021_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_meanGap_numerator_parse :
    SourceJson.intChars geometryRow021_meanGapNumeratorChars = some (1074023 : Int) := by decide +kernel

theorem geometryRow021_meanGap_denominator_parse :
    SourceJson.intChars geometryRow021_meanGapDenominatorChars = some (937125000 : Int) := by decide +kernel

theorem geometryRow021_meanGap_denominator_nonzero : (937125000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_meanGap_parse :
    parseRational geometryRow021_meanGapText = .ok geometryRowsTyped021.meanGap :=
  original_rational_fraction_of_chars geometryRow021_meanGapNumeratorChars geometryRow021_meanGapDenominatorChars
    (1074023 : Int) (937125000 : Int)
    geometryRow021_meanGap_numerator_no_slash geometryRow021_meanGap_numerator_parse
    geometryRow021_meanGap_denominator_parse geometryRow021_meanGap_denominator_nonzero

theorem geometryRow021_meanGap_read :
    rationalField geometryRowsJson021 "mean_gap" = .ok geometryRowsTyped021.meanGap :=
  original_rationalField_of_string geometryRowsJson021 "mean_gap" geometryRow021_meanGapText
    geometryRowsTyped021.meanGap geometryRow021_meanGap_field geometryRow021_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_meanGap_complete"
  err.flush

noncomputable def geometryRow021_jensenBoundNumeratorChars : List Char := ['5', '3', '2', '6', '2', '8', '5', '5', '5', '2', '3', '1', '6', '0', '8', '7', '6', '4', '6', '0', '9', '7', '1', '3', '9', '2', '0', '3', '7', '1', '3', '5', '9', '1', '4', '7', '1', '4', '8', '8', '7', '8', '8', '1', '0', '7', '3', '9', '2', '8', '9', '4', '5', '6', '1', '4', '3', '8', '0', '6', '8', '3', '0', '7', '3', '5', '9', '5', '7', '2', '2', '6', '8', '4', '5', '4', '3', '7', '1', '2', '6', '0', '4', '7', '0', '2', '2', '7', '8', '2', '2', '9', '4', '7', '7', '0', '6', '1', '6', '5', '3', '2', '9', '5', '6', '4', '4', '4', '5', '8', '0', '2', '3', '3', '4', '7', '5', '4', '8', '4', '6', '5', '9', '2', '9', '9', '4', '9', '9', '2', '0', '8', '0', '0', '8', '1', '2', '1', '5', '8', '7', '8', '4', '7', '7', '1', '1', '9', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow021_jensenBoundDenominatorChars : List Char := ['5', '4', '1', '1', '4', '6', '1', '0', '8', '1', '0', '5', '5', '0', '8', '7', '1', '3', '9', '5', '1', '4', '5', '2', '3', '7', '0', '2', '2', '3', '3', '1', '2', '0', '8', '0', '3', '7', '7', '9', '1', '8', '1', '0', '6', '4', '0', '0', '2', '4', '7', '1', '1', '8', '7', '6', '8', '5', '6', '8', '5', '1', '3', '3', '0', '2', '8', '6', '4', '7', '2', '2', '0', '6', '1', '1', '1', '4', '6', '3', '4', '4', '2', '2', '1', '1', '3', '9', '4', '4', '0', '4', '1', '1', '9', '2', '3', '0', '8', '8', '2', '9', '4', '4', '7', '7', '1', '2', '3', '1', '2', '0', '1', '0', '2', '7', '5', '2', '5', '8', '5', '5', '4', '4', '3', '4', '4', '3', '7', '5', '2', '2', '0', '1', '2', '9', '1', '0', '1', '5', '7', '2', '0', '8', '3', '6', '6', '7', '5', '7', '0', '0', '5', '9', '9', '9', '1', '3', '1', '2', '6', '9', '2', '7', '1', '9', '4', '4', '1', '1', '1', '3', '0', '6', '5', '1', '2', '0', '9', '3', '1', '2', '9', '8', '9', '7']
noncomputable def geometryRow021_jensenBoundText : String := String.ofList (geometryRow021_jensenBoundNumeratorChars ++ '/' :: geometryRow021_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_jensenBound_before_field"
  err.flush

theorem geometryRow021_jensenBound_field :
    geometryRowsJson021.getObjVal? "jensen_bound" = .ok (.str geometryRow021_jensenBoundText) := by rfl

theorem geometryRow021_jensenBound_numerator_no_slash :
    geometryRow021_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow021_jensenBoundNumeratorChars = some (53262855523160876460971392037135914714887881073928945614380683073595722684543712604702278229477061653295644458023347548465929949920800812158784771194880000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow021_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow021_jensenBoundDenominatorChars = some (541146108105508713951452370223312080377918106400247118768568513302864722061114634422113944041192308829447712312010275258554434437522012910157208366757005999131269271944111306512093129897 : Int) := by decide +kernel

theorem geometryRow021_jensenBound_denominator_nonzero : (541146108105508713951452370223312080377918106400247118768568513302864722061114634422113944041192308829447712312010275258554434437522012910157208366757005999131269271944111306512093129897 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_jensenBound_parse :
    parseRational geometryRow021_jensenBoundText = .ok geometryRowsTyped021.jensenBound :=
  original_rational_fraction_of_chars geometryRow021_jensenBoundNumeratorChars geometryRow021_jensenBoundDenominatorChars
    (53262855523160876460971392037135914714887881073928945614380683073595722684543712604702278229477061653295644458023347548465929949920800812158784771194880000000000000000000000000 : Int) (541146108105508713951452370223312080377918106400247118768568513302864722061114634422113944041192308829447712312010275258554434437522012910157208366757005999131269271944111306512093129897 : Int)
    geometryRow021_jensenBound_numerator_no_slash geometryRow021_jensenBound_numerator_parse
    geometryRow021_jensenBound_denominator_parse geometryRow021_jensenBound_denominator_nonzero

theorem geometryRow021_jensenBound_read :
    rationalField geometryRowsJson021 "jensen_bound" = .ok geometryRowsTyped021.jensenBound :=
  original_rationalField_of_string geometryRowsJson021 "jensen_bound" geometryRow021_jensenBoundText
    geometryRowsTyped021.jensenBound geometryRow021_jensenBound_field geometryRow021_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_factorMaxima_before"
  err.flush

theorem geometryRow021_factorMaxima_read :
    rationalArrayField geometryRowsJson021 "factor_maxima" = .ok geometryRowsTyped021.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_gapWeightedMeans_before"
  err.flush

theorem geometryRow021_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson021 "gap_weighted_means" = .ok geometryRowsTyped021.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow021_floorChars : List Char := ['7', '7', '9', '8', '1', '1', '2', '3', '9', '5', '4', '4', '2', '0', '1', '4', '2', '9', '6']
noncomputable def geometryRow021_floorText : String := String.ofList geometryRow021_floorChars

theorem geometryRow021_floor_text_read :
    geometryRowsJson021.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow021_floorText := by rfl

theorem geometryRow021_floor_chars_parse :
    SourceJson.intChars geometryRow021_floorChars = some (7798112395442014296 : Int) := by decide +kernel

theorem geometryRow021_floor_parse :
    parseInteger geometryRow021_floorText = .ok geometryRowsTyped021.jensenFloorQ96 := by
  simp only [geometryRow021_floorText, parseInteger, String.toList_ofList, geometryRow021_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_021 :
    decodeGeometryRow geometryRowsJson021 = .ok geometryRowsTyped021 :=
  original_geometryRow_of_fields geometryRowsJson021 geometryRowsTyped021 geometryRow021_floorText
    geometryRow021_simplexId_read geometryRow021_vertexIds_read
    geometryRow021_physicalVolume_read geometryRow021_meanGap_read
    geometryRow021_factorMaxima_read geometryRow021_gapWeightedMeans_read
    geometryRow021_jensenBound_read geometryRow021_floor_text_read geometryRow021_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_021_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock010 : List SourceJson := [geometryRowsJson020, geometryRowsJson021]
noncomputable def geometryRowsTypedBlock010 : List (GeometryRow) := [geometryRowsTyped020, geometryRowsTyped021]
noncomputable def geometryRowsTypedThroughBlock010 : List (GeometryRow) := geometryRowsTypedThroughBlock009 ++ geometryRowsTypedBlock010

theorem geometry_Rows_block_010_push_eq (acc : List SourceJson) :
    SimplicesBlock010.blockPush acc = [geometryRowsJson021, geometryRowsJson020] ++ acc := by rfl

theorem geometry_Rows_block_010_reverse (acc : List SourceJson) :
    (SimplicesBlock010.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock010 := by
  rw [geometry_Rows_block_010_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_010 :
    geometryRowsJsonBlock010.mapM decodeGeometryRow = .ok geometryRowsTypedBlock010 := by
  simp only [geometryRowsJsonBlock010, geometryRowsTypedBlock010, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_020, decode_geometry_Rows_021]
  rfl

theorem decode_geometry_Rows_through_block_010 :
    SimplicesValue.arrayAcc011.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock010 := by
  change (SimplicesBlock010.blockPush SimplicesValue.arrayAcc010).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_010_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_009, decode_geometry_Rows_block_010]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_010_complete"
  err.flush

#print axioms geometryRow020_simplexId_read
#print axioms geometryRow020_vertexIds_read
#print axioms geometryRow020_physicalVolume_field
#print axioms geometryRow020_physicalVolume_numerator_no_slash
#print axioms geometryRow020_physicalVolume_numerator_parse
#print axioms geometryRow020_physicalVolume_denominator_parse
#print axioms geometryRow020_physicalVolume_denominator_nonzero
#print axioms geometryRow020_physicalVolume_parse
#print axioms geometryRow020_physicalVolume_read
#print axioms geometryRow020_meanGap_field
#print axioms geometryRow020_meanGap_numerator_no_slash
#print axioms geometryRow020_meanGap_numerator_parse
#print axioms geometryRow020_meanGap_denominator_parse
#print axioms geometryRow020_meanGap_denominator_nonzero
#print axioms geometryRow020_meanGap_parse
#print axioms geometryRow020_meanGap_read
#print axioms geometryRow020_jensenBound_field
#print axioms geometryRow020_jensenBound_numerator_no_slash
#print axioms geometryRow020_jensenBound_numerator_parse
#print axioms geometryRow020_jensenBound_denominator_parse
#print axioms geometryRow020_jensenBound_denominator_nonzero
#print axioms geometryRow020_jensenBound_parse
#print axioms geometryRow020_jensenBound_read
#print axioms geometryRow020_factorMaxima_read
#print axioms geometryRow020_gapWeightedMeans_read
#print axioms geometryRow020_floor_text_read
#print axioms geometryRow020_floor_chars_parse
#print axioms geometryRow020_floor_parse
#print axioms decode_geometry_Rows_020
#print axioms geometryRow021_simplexId_read
#print axioms geometryRow021_vertexIds_read
#print axioms geometryRow021_physicalVolume_field
#print axioms geometryRow021_physicalVolume_numerator_no_slash
#print axioms geometryRow021_physicalVolume_numerator_parse
#print axioms geometryRow021_physicalVolume_denominator_parse
#print axioms geometryRow021_physicalVolume_denominator_nonzero
#print axioms geometryRow021_physicalVolume_parse
#print axioms geometryRow021_physicalVolume_read
#print axioms geometryRow021_meanGap_field
#print axioms geometryRow021_meanGap_numerator_no_slash
#print axioms geometryRow021_meanGap_numerator_parse
#print axioms geometryRow021_meanGap_denominator_parse
#print axioms geometryRow021_meanGap_denominator_nonzero
#print axioms geometryRow021_meanGap_parse
#print axioms geometryRow021_meanGap_read
#print axioms geometryRow021_jensenBound_field
#print axioms geometryRow021_jensenBound_numerator_no_slash
#print axioms geometryRow021_jensenBound_numerator_parse
#print axioms geometryRow021_jensenBound_denominator_parse
#print axioms geometryRow021_jensenBound_denominator_nonzero
#print axioms geometryRow021_jensenBound_parse
#print axioms geometryRow021_jensenBound_read
#print axioms geometryRow021_factorMaxima_read
#print axioms geometryRow021_gapWeightedMeans_read
#print axioms geometryRow021_floor_text_read
#print axioms geometryRow021_floor_chars_parse
#print axioms geometryRow021_floor_parse
#print axioms decode_geometry_Rows_021
#print axioms geometry_Rows_block_010_push_eq
#print axioms geometry_Rows_block_010_reverse
#print axioms decode_geometry_Rows_block_010
#print axioms decode_geometry_Rows_through_block_010

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
