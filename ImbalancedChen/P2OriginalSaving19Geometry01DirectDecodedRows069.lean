import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows068

/-! Original simplices typed block 69, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson136 : SourceJson :=
  (SimplicesBlock069.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped136 : GeometryRow :=
  { simplexId := 136,
    vertexIds := #[39, 38, 32, 30, 24, 23, 21, 20, 16],
    physicalVolume := ((25279525091895274819169139541201698883831 : ℚ) / (29498759210266214400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((496879 : ℚ) / (5600000 : ℚ)), ((496879 : ℚ) / (5600000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1921471 : ℚ) / (30000000 : ℚ)), ((5577817 : ℚ) / (108000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((18497785743239 : ℚ) / (262006200000000 : ℚ)), ((18546708810749 : ℚ) / (262006200000000 : ℚ)), ((13102702093387 : ℚ) / (87335400000000 : ℚ)), ((85067166484349 : ℚ) / (786018600000000 : ℚ)), ((4663430188699 : ℚ) / (87335400000000 : ℚ)), ((3910891879187 : ℚ) / (87335400000000 : ℚ)), ((1790312161429 : ℚ) / (41369400000000 : ℚ)), ((33596222645881 : ℚ) / (786018600000000 : ℚ)), ((16576157599817 : ℚ) / (393009300000000 : ℚ)), ((16576131399197 : ℚ) / (393009300000000 : ℚ))],
    jensenBound := ((3145541655451053906365376168151932083511498518106611241460398270908707483873786744387980855562500000000000000000000 : ℚ) / (5647718760655494983469834447633206108428260144706040791283225680808051515179774665044349218241609278302615577531136120278229515391941 : ℚ)),
    jensenFloorQ96 := (44126752063 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_simplexId_before"
  err.flush

theorem geometryRow136_simplexId_read :
    geometryRowsJson136.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped136.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_vertexIds_before"
  err.flush

theorem geometryRow136_vertexIds_read :
    geometryRowsJson136.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped136.vertexIds := by decide +kernel

noncomputable def geometryRow136_physicalVolumeNumeratorChars : List Char := ['2', '5', '2', '7', '9', '5', '2', '5', '0', '9', '1', '8', '9', '5', '2', '7', '4', '8', '1', '9', '1', '6', '9', '1', '3', '9', '5', '4', '1', '2', '0', '1', '6', '9', '8', '8', '8', '3', '8', '3', '1']
noncomputable def geometryRow136_physicalVolumeDenominatorChars : List Char := ['2', '9', '4', '9', '8', '7', '5', '9', '2', '1', '0', '2', '6', '6', '2', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow136_physicalVolumeText : String := String.ofList (geometryRow136_physicalVolumeNumeratorChars ++ '/' :: geometryRow136_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_physicalVolume_before_field"
  err.flush

theorem geometryRow136_physicalVolume_field :
    geometryRowsJson136.getObjVal? "physical_volume" = .ok (.str geometryRow136_physicalVolumeText) := by rfl

theorem geometryRow136_physicalVolume_numerator_no_slash :
    geometryRow136_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow136_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow136_physicalVolumeNumeratorChars = some (25279525091895274819169139541201698883831 : Int) := by decide +kernel

theorem geometryRow136_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow136_physicalVolumeDenominatorChars = some (29498759210266214400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow136_physicalVolume_denominator_nonzero : (29498759210266214400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow136_physicalVolume_parse :
    parseRational geometryRow136_physicalVolumeText = .ok geometryRowsTyped136.physicalVolume :=
  original_rational_fraction_of_chars geometryRow136_physicalVolumeNumeratorChars geometryRow136_physicalVolumeDenominatorChars
    (25279525091895274819169139541201698883831 : Int) (29498759210266214400000000000000000000000000000000000000000000000000 : Int)
    geometryRow136_physicalVolume_numerator_no_slash geometryRow136_physicalVolume_numerator_parse
    geometryRow136_physicalVolume_denominator_parse geometryRow136_physicalVolume_denominator_nonzero

theorem geometryRow136_physicalVolume_read :
    rationalField geometryRowsJson136 "physical_volume" = .ok geometryRowsTyped136.physicalVolume :=
  original_rationalField_of_string geometryRowsJson136 "physical_volume" geometryRow136_physicalVolumeText
    geometryRowsTyped136.physicalVolume geometryRow136_physicalVolume_field geometryRow136_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_physicalVolume_complete"
  err.flush

noncomputable def geometryRow136_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow136_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow136_meanGapText : String := String.ofList (geometryRow136_meanGapNumeratorChars ++ '/' :: geometryRow136_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_meanGap_before_field"
  err.flush

theorem geometryRow136_meanGap_field :
    geometryRowsJson136.getObjVal? "mean_gap" = .ok (.str geometryRow136_meanGapText) := by rfl

theorem geometryRow136_meanGap_numerator_no_slash :
    geometryRow136_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow136_meanGap_numerator_parse :
    SourceJson.intChars geometryRow136_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow136_meanGap_denominator_parse :
    SourceJson.intChars geometryRow136_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow136_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow136_meanGap_parse :
    parseRational geometryRow136_meanGapText = .ok geometryRowsTyped136.meanGap :=
  original_rational_fraction_of_chars geometryRow136_meanGapNumeratorChars geometryRow136_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow136_meanGap_numerator_no_slash geometryRow136_meanGap_numerator_parse
    geometryRow136_meanGap_denominator_parse geometryRow136_meanGap_denominator_nonzero

theorem geometryRow136_meanGap_read :
    rationalField geometryRowsJson136 "mean_gap" = .ok geometryRowsTyped136.meanGap :=
  original_rationalField_of_string geometryRowsJson136 "mean_gap" geometryRow136_meanGapText
    geometryRowsTyped136.meanGap geometryRow136_meanGap_field geometryRow136_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_meanGap_complete"
  err.flush

noncomputable def geometryRow136_jensenBoundNumeratorChars : List Char := ['3', '1', '4', '5', '5', '4', '1', '6', '5', '5', '4', '5', '1', '0', '5', '3', '9', '0', '6', '3', '6', '5', '3', '7', '6', '1', '6', '8', '1', '5', '1', '9', '3', '2', '0', '8', '3', '5', '1', '1', '4', '9', '8', '5', '1', '8', '1', '0', '6', '6', '1', '1', '2', '4', '1', '4', '6', '0', '3', '9', '8', '2', '7', '0', '9', '0', '8', '7', '0', '7', '4', '8', '3', '8', '7', '3', '7', '8', '6', '7', '4', '4', '3', '8', '7', '9', '8', '0', '8', '5', '5', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow136_jensenBoundDenominatorChars : List Char := ['5', '6', '4', '7', '7', '1', '8', '7', '6', '0', '6', '5', '5', '4', '9', '4', '9', '8', '3', '4', '6', '9', '8', '3', '4', '4', '4', '7', '6', '3', '3', '2', '0', '6', '1', '0', '8', '4', '2', '8', '2', '6', '0', '1', '4', '4', '7', '0', '6', '0', '4', '0', '7', '9', '1', '2', '8', '3', '2', '2', '5', '6', '8', '0', '8', '0', '8', '0', '5', '1', '5', '1', '5', '1', '7', '9', '7', '7', '4', '6', '6', '5', '0', '4', '4', '3', '4', '9', '2', '1', '8', '2', '4', '1', '6', '0', '9', '2', '7', '8', '3', '0', '2', '6', '1', '5', '5', '7', '7', '5', '3', '1', '1', '3', '6', '1', '2', '0', '2', '7', '8', '2', '2', '9', '5', '1', '5', '3', '9', '1', '9', '4', '1']
noncomputable def geometryRow136_jensenBoundText : String := String.ofList (geometryRow136_jensenBoundNumeratorChars ++ '/' :: geometryRow136_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_jensenBound_before_field"
  err.flush

theorem geometryRow136_jensenBound_field :
    geometryRowsJson136.getObjVal? "jensen_bound" = .ok (.str geometryRow136_jensenBoundText) := by rfl

theorem geometryRow136_jensenBound_numerator_no_slash :
    geometryRow136_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow136_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow136_jensenBoundNumeratorChars = some (3145541655451053906365376168151932083511498518106611241460398270908707483873786744387980855562500000000000000000000 : Int) := by decide +kernel

theorem geometryRow136_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow136_jensenBoundDenominatorChars = some (5647718760655494983469834447633206108428260144706040791283225680808051515179774665044349218241609278302615577531136120278229515391941 : Int) := by decide +kernel

theorem geometryRow136_jensenBound_denominator_nonzero : (5647718760655494983469834447633206108428260144706040791283225680808051515179774665044349218241609278302615577531136120278229515391941 : Int) ≠ 0 := by decide +kernel

theorem geometryRow136_jensenBound_parse :
    parseRational geometryRow136_jensenBoundText = .ok geometryRowsTyped136.jensenBound :=
  original_rational_fraction_of_chars geometryRow136_jensenBoundNumeratorChars geometryRow136_jensenBoundDenominatorChars
    (3145541655451053906365376168151932083511498518106611241460398270908707483873786744387980855562500000000000000000000 : Int) (5647718760655494983469834447633206108428260144706040791283225680808051515179774665044349218241609278302615577531136120278229515391941 : Int)
    geometryRow136_jensenBound_numerator_no_slash geometryRow136_jensenBound_numerator_parse
    geometryRow136_jensenBound_denominator_parse geometryRow136_jensenBound_denominator_nonzero

theorem geometryRow136_jensenBound_read :
    rationalField geometryRowsJson136 "jensen_bound" = .ok geometryRowsTyped136.jensenBound :=
  original_rationalField_of_string geometryRowsJson136 "jensen_bound" geometryRow136_jensenBoundText
    geometryRowsTyped136.jensenBound geometryRow136_jensenBound_field geometryRow136_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_factorMaxima_before"
  err.flush

theorem geometryRow136_factorMaxima_read :
    rationalArrayField geometryRowsJson136 "factor_maxima" = .ok geometryRowsTyped136.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_gapWeightedMeans_before"
  err.flush

theorem geometryRow136_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson136 "gap_weighted_means" = .ok geometryRowsTyped136.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow136_floorChars : List Char := ['4', '4', '1', '2', '6', '7', '5', '2', '0', '6', '3']
noncomputable def geometryRow136_floorText : String := String.ofList geometryRow136_floorChars

theorem geometryRow136_floor_text_read :
    geometryRowsJson136.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow136_floorText := by rfl

theorem geometryRow136_floor_chars_parse :
    SourceJson.intChars geometryRow136_floorChars = some (44126752063 : Int) := by decide +kernel

theorem geometryRow136_floor_parse :
    parseInteger geometryRow136_floorText = .ok geometryRowsTyped136.jensenFloorQ96 := by
  simp only [geometryRow136_floorText, parseInteger, String.toList_ofList, geometryRow136_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_136 :
    decodeGeometryRow geometryRowsJson136 = .ok geometryRowsTyped136 :=
  original_geometryRow_of_fields geometryRowsJson136 geometryRowsTyped136 geometryRow136_floorText
    geometryRow136_simplexId_read geometryRow136_vertexIds_read
    geometryRow136_physicalVolume_read geometryRow136_meanGap_read
    geometryRow136_factorMaxima_read geometryRow136_gapWeightedMeans_read
    geometryRow136_jensenBound_read geometryRow136_floor_text_read geometryRow136_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_136_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson137 : SourceJson :=
  (SimplicesBlock069.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped137 : GeometryRow :=
  { simplexId := 137,
    vertexIds := #[39, 33, 31, 24, 23, 19, 18, 15, 14],
    physicalVolume := ((616152601854382551843976067726978025397488677 : ℚ) / (33329277635073225523200000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1921543 : ℚ) / (30000000 : ℚ)), ((734331 : ℚ) / (14000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((82135607821 : ℚ) / (1188450000000 : ℚ)), ((164791755887 : ℚ) / (2376900000000 : ℚ)), ((29230586329 : ℚ) / (198075000000 : ℚ)), ((10515243004117 : ℚ) / (99829800000000 : ℚ)), ((587280688367 : ℚ) / (11092200000000 : ℚ)), ((37301623589 : ℚ) / (792300000000 : ℚ)), ((234579125441 : ℚ) / (5254200000000 : ℚ)), ((4403697510269 : ℚ) / (99829800000000 : ℚ)), ((2188515631537 : ℚ) / (49914900000000 : ℚ)), ((4260897545879 : ℚ) / (99829800000000 : ℚ))],
    jensenBound := ((15411953928112355263823072324742844619323523170222161326263743466862778653655715942382812500000000000 : ℚ) / (1172122551392429369741899622203947187461504841114748568867755058472627173555478482120979684374403291216363818535019 : ℚ)),
    jensenFloorQ96 := (1041751810873593 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_simplexId_before"
  err.flush

theorem geometryRow137_simplexId_read :
    geometryRowsJson137.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped137.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_vertexIds_before"
  err.flush

theorem geometryRow137_vertexIds_read :
    geometryRowsJson137.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped137.vertexIds := by decide +kernel

noncomputable def geometryRow137_physicalVolumeNumeratorChars : List Char := ['6', '1', '6', '1', '5', '2', '6', '0', '1', '8', '5', '4', '3', '8', '2', '5', '5', '1', '8', '4', '3', '9', '7', '6', '0', '6', '7', '7', '2', '6', '9', '7', '8', '0', '2', '5', '3', '9', '7', '4', '8', '8', '6', '7', '7']
noncomputable def geometryRow137_physicalVolumeDenominatorChars : List Char := ['3', '3', '3', '2', '9', '2', '7', '7', '6', '3', '5', '0', '7', '3', '2', '2', '5', '5', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow137_physicalVolumeText : String := String.ofList (geometryRow137_physicalVolumeNumeratorChars ++ '/' :: geometryRow137_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_physicalVolume_before_field"
  err.flush

theorem geometryRow137_physicalVolume_field :
    geometryRowsJson137.getObjVal? "physical_volume" = .ok (.str geometryRow137_physicalVolumeText) := by rfl

theorem geometryRow137_physicalVolume_numerator_no_slash :
    geometryRow137_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow137_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow137_physicalVolumeNumeratorChars = some (616152601854382551843976067726978025397488677 : Int) := by decide +kernel

theorem geometryRow137_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow137_physicalVolumeDenominatorChars = some (33329277635073225523200000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow137_physicalVolume_denominator_nonzero : (33329277635073225523200000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow137_physicalVolume_parse :
    parseRational geometryRow137_physicalVolumeText = .ok geometryRowsTyped137.physicalVolume :=
  original_rational_fraction_of_chars geometryRow137_physicalVolumeNumeratorChars geometryRow137_physicalVolumeDenominatorChars
    (616152601854382551843976067726978025397488677 : Int) (33329277635073225523200000000000000000000000000000000000000000000000 : Int)
    geometryRow137_physicalVolume_numerator_no_slash geometryRow137_physicalVolume_numerator_parse
    geometryRow137_physicalVolume_denominator_parse geometryRow137_physicalVolume_denominator_nonzero

theorem geometryRow137_physicalVolume_read :
    rationalField geometryRowsJson137 "physical_volume" = .ok geometryRowsTyped137.physicalVolume :=
  original_rationalField_of_string geometryRowsJson137 "physical_volume" geometryRow137_physicalVolumeText
    geometryRowsTyped137.physicalVolume geometryRow137_physicalVolume_field geometryRow137_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_physicalVolume_complete"
  err.flush

noncomputable def geometryRow137_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow137_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow137_meanGapText : String := String.ofList (geometryRow137_meanGapNumeratorChars ++ '/' :: geometryRow137_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_meanGap_before_field"
  err.flush

theorem geometryRow137_meanGap_field :
    geometryRowsJson137.getObjVal? "mean_gap" = .ok (.str geometryRow137_meanGapText) := by rfl

theorem geometryRow137_meanGap_numerator_no_slash :
    geometryRow137_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow137_meanGap_numerator_parse :
    SourceJson.intChars geometryRow137_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow137_meanGap_denominator_parse :
    SourceJson.intChars geometryRow137_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow137_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow137_meanGap_parse :
    parseRational geometryRow137_meanGapText = .ok geometryRowsTyped137.meanGap :=
  original_rational_fraction_of_chars geometryRow137_meanGapNumeratorChars geometryRow137_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow137_meanGap_numerator_no_slash geometryRow137_meanGap_numerator_parse
    geometryRow137_meanGap_denominator_parse geometryRow137_meanGap_denominator_nonzero

theorem geometryRow137_meanGap_read :
    rationalField geometryRowsJson137 "mean_gap" = .ok geometryRowsTyped137.meanGap :=
  original_rationalField_of_string geometryRowsJson137 "mean_gap" geometryRow137_meanGapText
    geometryRowsTyped137.meanGap geometryRow137_meanGap_field geometryRow137_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_meanGap_complete"
  err.flush

noncomputable def geometryRow137_jensenBoundNumeratorChars : List Char := ['1', '5', '4', '1', '1', '9', '5', '3', '9', '2', '8', '1', '1', '2', '3', '5', '5', '2', '6', '3', '8', '2', '3', '0', '7', '2', '3', '2', '4', '7', '4', '2', '8', '4', '4', '6', '1', '9', '3', '2', '3', '5', '2', '3', '1', '7', '0', '2', '2', '2', '1', '6', '1', '3', '2', '6', '2', '6', '3', '7', '4', '3', '4', '6', '6', '8', '6', '2', '7', '7', '8', '6', '5', '3', '6', '5', '5', '7', '1', '5', '9', '4', '2', '3', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow137_jensenBoundDenominatorChars : List Char := ['1', '1', '7', '2', '1', '2', '2', '5', '5', '1', '3', '9', '2', '4', '2', '9', '3', '6', '9', '7', '4', '1', '8', '9', '9', '6', '2', '2', '2', '0', '3', '9', '4', '7', '1', '8', '7', '4', '6', '1', '5', '0', '4', '8', '4', '1', '1', '1', '4', '7', '4', '8', '5', '6', '8', '8', '6', '7', '7', '5', '5', '0', '5', '8', '4', '7', '2', '6', '2', '7', '1', '7', '3', '5', '5', '5', '4', '7', '8', '4', '8', '2', '1', '2', '0', '9', '7', '9', '6', '8', '4', '3', '7', '4', '4', '0', '3', '2', '9', '1', '2', '1', '6', '3', '6', '3', '8', '1', '8', '5', '3', '5', '0', '1', '9']
noncomputable def geometryRow137_jensenBoundText : String := String.ofList (geometryRow137_jensenBoundNumeratorChars ++ '/' :: geometryRow137_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_jensenBound_before_field"
  err.flush

theorem geometryRow137_jensenBound_field :
    geometryRowsJson137.getObjVal? "jensen_bound" = .ok (.str geometryRow137_jensenBoundText) := by rfl

theorem geometryRow137_jensenBound_numerator_no_slash :
    geometryRow137_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow137_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow137_jensenBoundNumeratorChars = some (15411953928112355263823072324742844619323523170222161326263743466862778653655715942382812500000000000 : Int) := by decide +kernel

theorem geometryRow137_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow137_jensenBoundDenominatorChars = some (1172122551392429369741899622203947187461504841114748568867755058472627173555478482120979684374403291216363818535019 : Int) := by decide +kernel

theorem geometryRow137_jensenBound_denominator_nonzero : (1172122551392429369741899622203947187461504841114748568867755058472627173555478482120979684374403291216363818535019 : Int) ≠ 0 := by decide +kernel

theorem geometryRow137_jensenBound_parse :
    parseRational geometryRow137_jensenBoundText = .ok geometryRowsTyped137.jensenBound :=
  original_rational_fraction_of_chars geometryRow137_jensenBoundNumeratorChars geometryRow137_jensenBoundDenominatorChars
    (15411953928112355263823072324742844619323523170222161326263743466862778653655715942382812500000000000 : Int) (1172122551392429369741899622203947187461504841114748568867755058472627173555478482120979684374403291216363818535019 : Int)
    geometryRow137_jensenBound_numerator_no_slash geometryRow137_jensenBound_numerator_parse
    geometryRow137_jensenBound_denominator_parse geometryRow137_jensenBound_denominator_nonzero

theorem geometryRow137_jensenBound_read :
    rationalField geometryRowsJson137 "jensen_bound" = .ok geometryRowsTyped137.jensenBound :=
  original_rationalField_of_string geometryRowsJson137 "jensen_bound" geometryRow137_jensenBoundText
    geometryRowsTyped137.jensenBound geometryRow137_jensenBound_field geometryRow137_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_factorMaxima_before"
  err.flush

theorem geometryRow137_factorMaxima_read :
    rationalArrayField geometryRowsJson137 "factor_maxima" = .ok geometryRowsTyped137.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_gapWeightedMeans_before"
  err.flush

theorem geometryRow137_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson137 "gap_weighted_means" = .ok geometryRowsTyped137.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow137_floorChars : List Char := ['1', '0', '4', '1', '7', '5', '1', '8', '1', '0', '8', '7', '3', '5', '9', '3']
noncomputable def geometryRow137_floorText : String := String.ofList geometryRow137_floorChars

theorem geometryRow137_floor_text_read :
    geometryRowsJson137.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow137_floorText := by rfl

theorem geometryRow137_floor_chars_parse :
    SourceJson.intChars geometryRow137_floorChars = some (1041751810873593 : Int) := by decide +kernel

theorem geometryRow137_floor_parse :
    parseInteger geometryRow137_floorText = .ok geometryRowsTyped137.jensenFloorQ96 := by
  simp only [geometryRow137_floorText, parseInteger, String.toList_ofList, geometryRow137_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_137 :
    decodeGeometryRow geometryRowsJson137 = .ok geometryRowsTyped137 :=
  original_geometryRow_of_fields geometryRowsJson137 geometryRowsTyped137 geometryRow137_floorText
    geometryRow137_simplexId_read geometryRow137_vertexIds_read
    geometryRow137_physicalVolume_read geometryRow137_meanGap_read
    geometryRow137_factorMaxima_read geometryRow137_gapWeightedMeans_read
    geometryRow137_jensenBound_read geometryRow137_floor_text_read geometryRow137_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_137_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock069 : List SourceJson := [geometryRowsJson136, geometryRowsJson137]
noncomputable def geometryRowsTypedBlock069 : List (GeometryRow) := [geometryRowsTyped136, geometryRowsTyped137]
noncomputable def geometryRowsTypedThroughBlock069 : List (GeometryRow) := geometryRowsTypedThroughBlock068 ++ geometryRowsTypedBlock069

theorem geometry_Rows_block_069_push_eq (acc : List SourceJson) :
    SimplicesBlock069.blockPush acc = [geometryRowsJson137, geometryRowsJson136] ++ acc := by rfl

theorem geometry_Rows_block_069_reverse (acc : List SourceJson) :
    (SimplicesBlock069.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock069 := by
  rw [geometry_Rows_block_069_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_069 :
    geometryRowsJsonBlock069.mapM decodeGeometryRow = .ok geometryRowsTypedBlock069 := by
  simp only [geometryRowsJsonBlock069, geometryRowsTypedBlock069, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_136, decode_geometry_Rows_137]
  rfl

theorem decode_geometry_Rows_through_block_069 :
    SimplicesValue.arrayAcc070.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock069 := by
  change (SimplicesBlock069.blockPush SimplicesValue.arrayAcc069).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_069_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_068, decode_geometry_Rows_block_069]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_069_complete"
  err.flush

#print axioms geometryRow136_simplexId_read
#print axioms geometryRow136_vertexIds_read
#print axioms geometryRow136_physicalVolume_field
#print axioms geometryRow136_physicalVolume_numerator_no_slash
#print axioms geometryRow136_physicalVolume_numerator_parse
#print axioms geometryRow136_physicalVolume_denominator_parse
#print axioms geometryRow136_physicalVolume_denominator_nonzero
#print axioms geometryRow136_physicalVolume_parse
#print axioms geometryRow136_physicalVolume_read
#print axioms geometryRow136_meanGap_field
#print axioms geometryRow136_meanGap_numerator_no_slash
#print axioms geometryRow136_meanGap_numerator_parse
#print axioms geometryRow136_meanGap_denominator_parse
#print axioms geometryRow136_meanGap_denominator_nonzero
#print axioms geometryRow136_meanGap_parse
#print axioms geometryRow136_meanGap_read
#print axioms geometryRow136_jensenBound_field
#print axioms geometryRow136_jensenBound_numerator_no_slash
#print axioms geometryRow136_jensenBound_numerator_parse
#print axioms geometryRow136_jensenBound_denominator_parse
#print axioms geometryRow136_jensenBound_denominator_nonzero
#print axioms geometryRow136_jensenBound_parse
#print axioms geometryRow136_jensenBound_read
#print axioms geometryRow136_factorMaxima_read
#print axioms geometryRow136_gapWeightedMeans_read
#print axioms geometryRow136_floor_text_read
#print axioms geometryRow136_floor_chars_parse
#print axioms geometryRow136_floor_parse
#print axioms decode_geometry_Rows_136
#print axioms geometryRow137_simplexId_read
#print axioms geometryRow137_vertexIds_read
#print axioms geometryRow137_physicalVolume_field
#print axioms geometryRow137_physicalVolume_numerator_no_slash
#print axioms geometryRow137_physicalVolume_numerator_parse
#print axioms geometryRow137_physicalVolume_denominator_parse
#print axioms geometryRow137_physicalVolume_denominator_nonzero
#print axioms geometryRow137_physicalVolume_parse
#print axioms geometryRow137_physicalVolume_read
#print axioms geometryRow137_meanGap_field
#print axioms geometryRow137_meanGap_numerator_no_slash
#print axioms geometryRow137_meanGap_numerator_parse
#print axioms geometryRow137_meanGap_denominator_parse
#print axioms geometryRow137_meanGap_denominator_nonzero
#print axioms geometryRow137_meanGap_parse
#print axioms geometryRow137_meanGap_read
#print axioms geometryRow137_jensenBound_field
#print axioms geometryRow137_jensenBound_numerator_no_slash
#print axioms geometryRow137_jensenBound_numerator_parse
#print axioms geometryRow137_jensenBound_denominator_parse
#print axioms geometryRow137_jensenBound_denominator_nonzero
#print axioms geometryRow137_jensenBound_parse
#print axioms geometryRow137_jensenBound_read
#print axioms geometryRow137_factorMaxima_read
#print axioms geometryRow137_gapWeightedMeans_read
#print axioms geometryRow137_floor_text_read
#print axioms geometryRow137_floor_chars_parse
#print axioms geometryRow137_floor_parse
#print axioms decode_geometry_Rows_137
#print axioms geometry_Rows_block_069_push_eq
#print axioms geometry_Rows_block_069_reverse
#print axioms decode_geometry_Rows_block_069
#print axioms decode_geometry_Rows_through_block_069

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
