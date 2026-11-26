import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableSimplicesBlock000

/-! Local typed certificates for original cell 05, rows 0 through 7.
This owner imports only its own original parser leaf.  No cumulative typed
prefix, whole-array parser value, or completed geometric archive is imported.
The original rational decoder and GeometryRow record fields are unchanged. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson000 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped000 : GeometryRow :=
  { simplexId := 0,
    vertexIds := #[27, 13, 11, 9, 7, 5, 3, 1, 0],
    physicalVolume := ((908834610468788343749578255396396902013 : ℚ) / (35057735458357248000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((16828009 : ℚ) / (180000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((10683377097371 : ℚ) / (113240400000000 : ℚ)), ((10737999103901 : ℚ) / (113240400000000 : ℚ)), ((5312288542343 : ℚ) / (45296160000000 : ℚ)), ((58246088384443 : ℚ) / (679442400000000 : ℚ)), ((55227421806187 : ℚ) / (679442400000000 : ℚ)), ((695730297797 : ℚ) / (9059232000000 : ℚ)), ((14114665972699 : ℚ) / (339721200000000 : ℚ)), ((3862771438367 : ℚ) / (113240400000000 : ℚ)), ((1261908538929 : ℚ) / (37746800000000 : ℚ)), ((11047531356931 : ℚ) / (339721200000000 : ℚ))],
    jensenBound := ((3027260091070484128241619356525971428061982215594932457455218563040926631571577888417769600000000000000000000000 : ℚ) / (94242344544266739339137396057856067947389630455816189283203289864940756971064225017431384170430139149127087484219044236649104257 : ℚ)),
    jensenFloorQ96 := (2544973341103 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_simplexId_before"
  err.flush

theorem geometryRow000_simplexId_read :
    geometryRowsJson000.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped000.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_vertexIds_before"
  err.flush

theorem geometryRow000_vertexIds_read :
    geometryRowsJson000.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped000.vertexIds := by decide +kernel

noncomputable def geometryRow000_physicalVolumeNumeratorChars : List Char := ['9', '0', '8', '8', '3', '4', '6', '1', '0', '4', '6', '8', '7', '8', '8', '3', '4', '3', '7', '4', '9', '5', '7', '8', '2', '5', '5', '3', '9', '6', '3', '9', '6', '9', '0', '2', '0', '1', '3']
noncomputable def geometryRow000_physicalVolumeDenominatorChars : List Char := ['3', '5', '0', '5', '7', '7', '3', '5', '4', '5', '8', '3', '5', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_physicalVolumeText : String := String.ofList (geometryRow000_physicalVolumeNumeratorChars ++ '/' :: geometryRow000_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_physicalVolume_before_field"
  err.flush

theorem geometryRow000_physicalVolume_field :
    geometryRowsJson000.getObjVal? "physical_volume" = .ok (.str geometryRow000_physicalVolumeText) := by rfl

theorem geometryRow000_physicalVolume_numerator_no_slash :
    geometryRow000_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow000_physicalVolumeNumeratorChars = some (908834610468788343749578255396396902013 : Int) := by decide +kernel

theorem geometryRow000_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow000_physicalVolumeDenominatorChars = some (35057735458357248000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow000_physicalVolume_denominator_nonzero : (35057735458357248000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_physicalVolume_parse :
    parseRational geometryRow000_physicalVolumeText = .ok geometryRowsTyped000.physicalVolume :=
  original_rational_fraction_of_chars geometryRow000_physicalVolumeNumeratorChars geometryRow000_physicalVolumeDenominatorChars
    (908834610468788343749578255396396902013 : Int) (35057735458357248000000000000000000000000000000000000000000000000 : Int)
    geometryRow000_physicalVolume_numerator_no_slash geometryRow000_physicalVolume_numerator_parse
    geometryRow000_physicalVolume_denominator_parse geometryRow000_physicalVolume_denominator_nonzero

theorem geometryRow000_physicalVolume_read :
    rationalField geometryRowsJson000 "physical_volume" = .ok geometryRowsTyped000.physicalVolume :=
  original_rationalField_of_string geometryRowsJson000 "physical_volume" geometryRow000_physicalVolumeText
    geometryRowsTyped000.physicalVolume geometryRow000_physicalVolume_field geometryRow000_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_physicalVolume_complete"
  err.flush

noncomputable def geometryRow000_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow000_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_meanGapText : String := String.ofList (geometryRow000_meanGapNumeratorChars ++ '/' :: geometryRow000_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_meanGap_before_field"
  err.flush

theorem geometryRow000_meanGap_field :
    geometryRowsJson000.getObjVal? "mean_gap" = .ok (.str geometryRow000_meanGapText) := by rfl

theorem geometryRow000_meanGap_numerator_no_slash :
    geometryRow000_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_meanGap_numerator_parse :
    SourceJson.intChars geometryRow000_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow000_meanGap_denominator_parse :
    SourceJson.intChars geometryRow000_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow000_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_meanGap_parse :
    parseRational geometryRow000_meanGapText = .ok geometryRowsTyped000.meanGap :=
  original_rational_fraction_of_chars geometryRow000_meanGapNumeratorChars geometryRow000_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow000_meanGap_numerator_no_slash geometryRow000_meanGap_numerator_parse
    geometryRow000_meanGap_denominator_parse geometryRow000_meanGap_denominator_nonzero

theorem geometryRow000_meanGap_read :
    rationalField geometryRowsJson000 "mean_gap" = .ok geometryRowsTyped000.meanGap :=
  original_rationalField_of_string geometryRowsJson000 "mean_gap" geometryRow000_meanGapText
    geometryRowsTyped000.meanGap geometryRow000_meanGap_field geometryRow000_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_meanGap_complete"
  err.flush

noncomputable def geometryRow000_jensenBoundNumeratorChars : List Char := ['3', '0', '2', '7', '2', '6', '0', '0', '9', '1', '0', '7', '0', '4', '8', '4', '1', '2', '8', '2', '4', '1', '6', '1', '9', '3', '5', '6', '5', '2', '5', '9', '7', '1', '4', '2', '8', '0', '6', '1', '9', '8', '2', '2', '1', '5', '5', '9', '4', '9', '3', '2', '4', '5', '7', '4', '5', '5', '2', '1', '8', '5', '6', '3', '0', '4', '0', '9', '2', '6', '6', '3', '1', '5', '7', '1', '5', '7', '7', '8', '8', '8', '4', '1', '7', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_jensenBoundDenominatorChars : List Char := ['9', '4', '2', '4', '2', '3', '4', '4', '5', '4', '4', '2', '6', '6', '7', '3', '9', '3', '3', '9', '1', '3', '7', '3', '9', '6', '0', '5', '7', '8', '5', '6', '0', '6', '7', '9', '4', '7', '3', '8', '9', '6', '3', '0', '4', '5', '5', '8', '1', '6', '1', '8', '9', '2', '8', '3', '2', '0', '3', '2', '8', '9', '8', '6', '4', '9', '4', '0', '7', '5', '6', '9', '7', '1', '0', '6', '4', '2', '2', '5', '0', '1', '7', '4', '3', '1', '3', '8', '4', '1', '7', '0', '4', '3', '0', '1', '3', '9', '1', '4', '9', '1', '2', '7', '0', '8', '7', '4', '8', '4', '2', '1', '9', '0', '4', '4', '2', '3', '6', '6', '4', '9', '1', '0', '4', '2', '5', '7']
noncomputable def geometryRow000_jensenBoundText : String := String.ofList (geometryRow000_jensenBoundNumeratorChars ++ '/' :: geometryRow000_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_jensenBound_before_field"
  err.flush

theorem geometryRow000_jensenBound_field :
    geometryRowsJson000.getObjVal? "jensen_bound" = .ok (.str geometryRow000_jensenBoundText) := by rfl

theorem geometryRow000_jensenBound_numerator_no_slash :
    geometryRow000_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow000_jensenBoundNumeratorChars = some (3027260091070484128241619356525971428061982215594932457455218563040926631571577888417769600000000000000000000000 : Int) := by decide +kernel

theorem geometryRow000_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow000_jensenBoundDenominatorChars = some (94242344544266739339137396057856067947389630455816189283203289864940756971064225017431384170430139149127087484219044236649104257 : Int) := by decide +kernel

theorem geometryRow000_jensenBound_denominator_nonzero : (94242344544266739339137396057856067947389630455816189283203289864940756971064225017431384170430139149127087484219044236649104257 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_jensenBound_parse :
    parseRational geometryRow000_jensenBoundText = .ok geometryRowsTyped000.jensenBound :=
  original_rational_fraction_of_chars geometryRow000_jensenBoundNumeratorChars geometryRow000_jensenBoundDenominatorChars
    (3027260091070484128241619356525971428061982215594932457455218563040926631571577888417769600000000000000000000000 : Int) (94242344544266739339137396057856067947389630455816189283203289864940756971064225017431384170430139149127087484219044236649104257 : Int)
    geometryRow000_jensenBound_numerator_no_slash geometryRow000_jensenBound_numerator_parse
    geometryRow000_jensenBound_denominator_parse geometryRow000_jensenBound_denominator_nonzero

theorem geometryRow000_jensenBound_read :
    rationalField geometryRowsJson000 "jensen_bound" = .ok geometryRowsTyped000.jensenBound :=
  original_rationalField_of_string geometryRowsJson000 "jensen_bound" geometryRow000_jensenBoundText
    geometryRowsTyped000.jensenBound geometryRow000_jensenBound_field geometryRow000_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_factorMaxima_before"
  err.flush

theorem geometryRow000_factorMaxima_read :
    rationalArrayField geometryRowsJson000 "factor_maxima" = .ok geometryRowsTyped000.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_gapWeightedMeans_before"
  err.flush

theorem geometryRow000_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson000 "gap_weighted_means" = .ok geometryRowsTyped000.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow000_floorChars : List Char := ['2', '5', '4', '4', '9', '7', '3', '3', '4', '1', '1', '0', '3']
noncomputable def geometryRow000_floorText : String := String.ofList geometryRow000_floorChars

theorem geometryRow000_floor_text_read :
    geometryRowsJson000.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow000_floorText := by rfl

theorem geometryRow000_floor_chars_parse :
    SourceJson.intChars geometryRow000_floorChars = some (2544973341103 : Int) := by decide +kernel

theorem geometryRow000_floor_parse :
    parseInteger geometryRow000_floorText = .ok geometryRowsTyped000.jensenFloorQ96 := by
  simp only [geometryRow000_floorText, parseInteger, String.toList_ofList, geometryRow000_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_000 :
    decodeGeometryRow geometryRowsJson000 = .ok geometryRowsTyped000 :=
  original_geometryRow_of_fields geometryRowsJson000 geometryRowsTyped000 geometryRow000_floorText
    geometryRow000_simplexId_read geometryRow000_vertexIds_read
    geometryRow000_physicalVolume_read geometryRow000_meanGap_read
    geometryRow000_factorMaxima_read geometryRow000_gapWeightedMeans_read
    geometryRow000_jensenBound_read geometryRow000_floor_text_read geometryRow000_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_000_original_decoder_complete"
  err.flush

theorem geometryRow000_shape :
    geometryRowsTyped000.simplexId = 0 ∧
    geometryRowsTyped000.vertexIds.size = 9 ∧ geometryRowsTyped000.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped000.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped000.factorMaxima.size = 10 ∧ geometryRowsTyped000.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson001 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped001 : GeometryRow :=
  { simplexId := 1,
    vertexIds := #[27, 13, 11, 9, 7, 5, 3, 2, 0],
    physicalVolume := ((908856777099023465919175289021426006117 : ℚ) / (35057735458357248000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((16828009 : ℚ) / (180000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((2698479464929 : ℚ) / (28310100000000 : ℚ)), ((5424269933123 : ℚ) / (56620200000000 : ℚ)), ((7979486889749 : ℚ) / (67944240000000 : ℚ)), ((29067773811049 : ℚ) / (339721200000000 : ℚ)), ((27558440521921 : ℚ) / (339721200000000 : ℚ)), ((5206923157243 : ℚ) / (67944240000000 : ℚ)), ((2260323252149 : ℚ) / (56620200000000 : ℚ)), ((5849427538723 : ℚ) / (169860600000000 : ℚ)), ((5733870130393 : ℚ) / (169860600000000 : ℚ)), ((929839343273 : ℚ) / (28310100000000 : ℚ))],
    jensenBound := ((1097556367380168469710373275928353606621118778777163068363583247074100825741155020556969410156250000000000000000 : ℚ) / (34341767493947732553476865112354232619400299353907372627698705088574179216327490117091341230108009144940836579410023012329000403 : ℚ)),
    jensenFloorQ96 := (2532117028009 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_simplexId_before"
  err.flush

theorem geometryRow001_simplexId_read :
    geometryRowsJson001.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped001.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_vertexIds_before"
  err.flush

theorem geometryRow001_vertexIds_read :
    geometryRowsJson001.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped001.vertexIds := by decide +kernel

noncomputable def geometryRow001_physicalVolumeNumeratorChars : List Char := ['9', '0', '8', '8', '5', '6', '7', '7', '7', '0', '9', '9', '0', '2', '3', '4', '6', '5', '9', '1', '9', '1', '7', '5', '2', '8', '9', '0', '2', '1', '4', '2', '6', '0', '0', '6', '1', '1', '7']
noncomputable def geometryRow001_physicalVolumeDenominatorChars : List Char := ['3', '5', '0', '5', '7', '7', '3', '5', '4', '5', '8', '3', '5', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_physicalVolumeText : String := String.ofList (geometryRow001_physicalVolumeNumeratorChars ++ '/' :: geometryRow001_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_physicalVolume_before_field"
  err.flush

theorem geometryRow001_physicalVolume_field :
    geometryRowsJson001.getObjVal? "physical_volume" = .ok (.str geometryRow001_physicalVolumeText) := by rfl

theorem geometryRow001_physicalVolume_numerator_no_slash :
    geometryRow001_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow001_physicalVolumeNumeratorChars = some (908856777099023465919175289021426006117 : Int) := by decide +kernel

theorem geometryRow001_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow001_physicalVolumeDenominatorChars = some (35057735458357248000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow001_physicalVolume_denominator_nonzero : (35057735458357248000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_physicalVolume_parse :
    parseRational geometryRow001_physicalVolumeText = .ok geometryRowsTyped001.physicalVolume :=
  original_rational_fraction_of_chars geometryRow001_physicalVolumeNumeratorChars geometryRow001_physicalVolumeDenominatorChars
    (908856777099023465919175289021426006117 : Int) (35057735458357248000000000000000000000000000000000000000000000000 : Int)
    geometryRow001_physicalVolume_numerator_no_slash geometryRow001_physicalVolume_numerator_parse
    geometryRow001_physicalVolume_denominator_parse geometryRow001_physicalVolume_denominator_nonzero

theorem geometryRow001_physicalVolume_read :
    rationalField geometryRowsJson001 "physical_volume" = .ok geometryRowsTyped001.physicalVolume :=
  original_rationalField_of_string geometryRowsJson001 "physical_volume" geometryRow001_physicalVolumeText
    geometryRowsTyped001.physicalVolume geometryRow001_physicalVolume_field geometryRow001_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_physicalVolume_complete"
  err.flush

noncomputable def geometryRow001_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow001_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_meanGapText : String := String.ofList (geometryRow001_meanGapNumeratorChars ++ '/' :: geometryRow001_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_meanGap_before_field"
  err.flush

theorem geometryRow001_meanGap_field :
    geometryRowsJson001.getObjVal? "mean_gap" = .ok (.str geometryRow001_meanGapText) := by rfl

theorem geometryRow001_meanGap_numerator_no_slash :
    geometryRow001_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_meanGap_numerator_parse :
    SourceJson.intChars geometryRow001_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow001_meanGap_denominator_parse :
    SourceJson.intChars geometryRow001_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow001_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_meanGap_parse :
    parseRational geometryRow001_meanGapText = .ok geometryRowsTyped001.meanGap :=
  original_rational_fraction_of_chars geometryRow001_meanGapNumeratorChars geometryRow001_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow001_meanGap_numerator_no_slash geometryRow001_meanGap_numerator_parse
    geometryRow001_meanGap_denominator_parse geometryRow001_meanGap_denominator_nonzero

theorem geometryRow001_meanGap_read :
    rationalField geometryRowsJson001 "mean_gap" = .ok geometryRowsTyped001.meanGap :=
  original_rationalField_of_string geometryRowsJson001 "mean_gap" geometryRow001_meanGapText
    geometryRowsTyped001.meanGap geometryRow001_meanGap_field geometryRow001_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_meanGap_complete"
  err.flush

noncomputable def geometryRow001_jensenBoundNumeratorChars : List Char := ['1', '0', '9', '7', '5', '5', '6', '3', '6', '7', '3', '8', '0', '1', '6', '8', '4', '6', '9', '7', '1', '0', '3', '7', '3', '2', '7', '5', '9', '2', '8', '3', '5', '3', '6', '0', '6', '6', '2', '1', '1', '1', '8', '7', '7', '8', '7', '7', '7', '1', '6', '3', '0', '6', '8', '3', '6', '3', '5', '8', '3', '2', '4', '7', '0', '7', '4', '1', '0', '0', '8', '2', '5', '7', '4', '1', '1', '5', '5', '0', '2', '0', '5', '5', '6', '9', '6', '9', '4', '1', '0', '1', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_jensenBoundDenominatorChars : List Char := ['3', '4', '3', '4', '1', '7', '6', '7', '4', '9', '3', '9', '4', '7', '7', '3', '2', '5', '5', '3', '4', '7', '6', '8', '6', '5', '1', '1', '2', '3', '5', '4', '2', '3', '2', '6', '1', '9', '4', '0', '0', '2', '9', '9', '3', '5', '3', '9', '0', '7', '3', '7', '2', '6', '2', '7', '6', '9', '8', '7', '0', '5', '0', '8', '8', '5', '7', '4', '1', '7', '9', '2', '1', '6', '3', '2', '7', '4', '9', '0', '1', '1', '7', '0', '9', '1', '3', '4', '1', '2', '3', '0', '1', '0', '8', '0', '0', '9', '1', '4', '4', '9', '4', '0', '8', '3', '6', '5', '7', '9', '4', '1', '0', '0', '2', '3', '0', '1', '2', '3', '2', '9', '0', '0', '0', '4', '0', '3']
noncomputable def geometryRow001_jensenBoundText : String := String.ofList (geometryRow001_jensenBoundNumeratorChars ++ '/' :: geometryRow001_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_jensenBound_before_field"
  err.flush

theorem geometryRow001_jensenBound_field :
    geometryRowsJson001.getObjVal? "jensen_bound" = .ok (.str geometryRow001_jensenBoundText) := by rfl

theorem geometryRow001_jensenBound_numerator_no_slash :
    geometryRow001_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow001_jensenBoundNumeratorChars = some (1097556367380168469710373275928353606621118778777163068363583247074100825741155020556969410156250000000000000000 : Int) := by decide +kernel

theorem geometryRow001_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow001_jensenBoundDenominatorChars = some (34341767493947732553476865112354232619400299353907372627698705088574179216327490117091341230108009144940836579410023012329000403 : Int) := by decide +kernel

theorem geometryRow001_jensenBound_denominator_nonzero : (34341767493947732553476865112354232619400299353907372627698705088574179216327490117091341230108009144940836579410023012329000403 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_jensenBound_parse :
    parseRational geometryRow001_jensenBoundText = .ok geometryRowsTyped001.jensenBound :=
  original_rational_fraction_of_chars geometryRow001_jensenBoundNumeratorChars geometryRow001_jensenBoundDenominatorChars
    (1097556367380168469710373275928353606621118778777163068363583247074100825741155020556969410156250000000000000000 : Int) (34341767493947732553476865112354232619400299353907372627698705088574179216327490117091341230108009144940836579410023012329000403 : Int)
    geometryRow001_jensenBound_numerator_no_slash geometryRow001_jensenBound_numerator_parse
    geometryRow001_jensenBound_denominator_parse geometryRow001_jensenBound_denominator_nonzero

theorem geometryRow001_jensenBound_read :
    rationalField geometryRowsJson001 "jensen_bound" = .ok geometryRowsTyped001.jensenBound :=
  original_rationalField_of_string geometryRowsJson001 "jensen_bound" geometryRow001_jensenBoundText
    geometryRowsTyped001.jensenBound geometryRow001_jensenBound_field geometryRow001_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_factorMaxima_before"
  err.flush

theorem geometryRow001_factorMaxima_read :
    rationalArrayField geometryRowsJson001 "factor_maxima" = .ok geometryRowsTyped001.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_gapWeightedMeans_before"
  err.flush

theorem geometryRow001_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson001 "gap_weighted_means" = .ok geometryRowsTyped001.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow001_floorChars : List Char := ['2', '5', '3', '2', '1', '1', '7', '0', '2', '8', '0', '0', '9']
noncomputable def geometryRow001_floorText : String := String.ofList geometryRow001_floorChars

theorem geometryRow001_floor_text_read :
    geometryRowsJson001.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow001_floorText := by rfl

theorem geometryRow001_floor_chars_parse :
    SourceJson.intChars geometryRow001_floorChars = some (2532117028009 : Int) := by decide +kernel

theorem geometryRow001_floor_parse :
    parseInteger geometryRow001_floorText = .ok geometryRowsTyped001.jensenFloorQ96 := by
  simp only [geometryRow001_floorText, parseInteger, String.toList_ofList, geometryRow001_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_001 :
    decodeGeometryRow geometryRowsJson001 = .ok geometryRowsTyped001 :=
  original_geometryRow_of_fields geometryRowsJson001 geometryRowsTyped001 geometryRow001_floorText
    geometryRow001_simplexId_read geometryRow001_vertexIds_read
    geometryRow001_physicalVolume_read geometryRow001_meanGap_read
    geometryRow001_factorMaxima_read geometryRow001_gapWeightedMeans_read
    geometryRow001_jensenBound_read geometryRow001_floor_text_read geometryRow001_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_001_original_decoder_complete"
  err.flush

theorem geometryRow001_shape :
    geometryRowsTyped001.simplexId = 1 ∧
    geometryRowsTyped001.vertexIds.size = 9 ∧ geometryRowsTyped001.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped001.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped001.factorMaxima.size = 10 ∧ geometryRowsTyped001.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson002 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped002 : GeometryRow :=
  { simplexId := 2,
    vertexIds := #[27, 13, 11, 9, 7, 5, 4, 2, 0],
    physicalVolume := ((99412270045298098436976742183372291399610087 : ℚ) / (1495796712889909248000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((10824169 : ℚ) / (19584000000 : ℚ)),
    factorMaxima := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((16828009 : ℚ) / (180000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((308260643425438431829 : ℚ) / (3268621939273600000000 : ℚ)), ((4854691831857858721 : ℚ) / (51072217801150000000 : ℚ)), ((345637528291750976293 : ℚ) / (2941759745346240000000 : ℚ)), ((105893469154003726267 : ℚ) / (1225733227227600000000 : ℚ)), ((12448088752548702241 : ℚ) / (153216653403450000000 : ℚ)), ((55934198958702357017 : ℚ) / (735439936336560000000 : ℚ)), ((596476595227762331189 : ℚ) / (14708798726731200000000 : ℚ)), ((505455236857547398801 : ℚ) / (14708798726731200000000 : ℚ)), ((496668541927351820041 : ℚ) / (14708798726731200000000 : ℚ)), ((59931516691168045687 : ℚ) / (1838599840841400000000 : ℚ))],
    jensenBound := ((58310283882295854222789409344453044063897875912947721410997251482104546467271061678484747219554871331790264442642066865273975536543423643634752723779736104769219284820312500000000000000000 : ℚ) / (342253535636489084744043376018114517135047411062342455363575197930869145184249394388138267361858214326435758467955162563309912633288227071805359524476846618728665155081743960627371148192232979499084169 : ℚ)),
    jensenFloorQ96 := (13498229139073607 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_simplexId_before"
  err.flush

theorem geometryRow002_simplexId_read :
    geometryRowsJson002.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped002.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_vertexIds_before"
  err.flush

theorem geometryRow002_vertexIds_read :
    geometryRowsJson002.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped002.vertexIds := by decide +kernel

noncomputable def geometryRow002_physicalVolumeNumeratorChars : List Char := ['9', '9', '4', '1', '2', '2', '7', '0', '0', '4', '5', '2', '9', '8', '0', '9', '8', '4', '3', '6', '9', '7', '6', '7', '4', '2', '1', '8', '3', '3', '7', '2', '2', '9', '1', '3', '9', '9', '6', '1', '0', '0', '8', '7']
noncomputable def geometryRow002_physicalVolumeDenominatorChars : List Char := ['1', '4', '9', '5', '7', '9', '6', '7', '1', '2', '8', '8', '9', '9', '0', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_physicalVolumeText : String := String.ofList (geometryRow002_physicalVolumeNumeratorChars ++ '/' :: geometryRow002_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_physicalVolume_before_field"
  err.flush

theorem geometryRow002_physicalVolume_field :
    geometryRowsJson002.getObjVal? "physical_volume" = .ok (.str geometryRow002_physicalVolumeText) := by rfl

theorem geometryRow002_physicalVolume_numerator_no_slash :
    geometryRow002_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow002_physicalVolumeNumeratorChars = some (99412270045298098436976742183372291399610087 : Int) := by decide +kernel

theorem geometryRow002_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow002_physicalVolumeDenominatorChars = some (1495796712889909248000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow002_physicalVolume_denominator_nonzero : (1495796712889909248000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_physicalVolume_parse :
    parseRational geometryRow002_physicalVolumeText = .ok geometryRowsTyped002.physicalVolume :=
  original_rational_fraction_of_chars geometryRow002_physicalVolumeNumeratorChars geometryRow002_physicalVolumeDenominatorChars
    (99412270045298098436976742183372291399610087 : Int) (1495796712889909248000000000000000000000000000000000000000000000000 : Int)
    geometryRow002_physicalVolume_numerator_no_slash geometryRow002_physicalVolume_numerator_parse
    geometryRow002_physicalVolume_denominator_parse geometryRow002_physicalVolume_denominator_nonzero

theorem geometryRow002_physicalVolume_read :
    rationalField geometryRowsJson002 "physical_volume" = .ok geometryRowsTyped002.physicalVolume :=
  original_rationalField_of_string geometryRowsJson002 "physical_volume" geometryRow002_physicalVolumeText
    geometryRowsTyped002.physicalVolume geometryRow002_physicalVolume_field geometryRow002_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_physicalVolume_complete"
  err.flush

noncomputable def geometryRow002_meanGapNumeratorChars : List Char := ['1', '0', '8', '2', '4', '1', '6', '9']
noncomputable def geometryRow002_meanGapDenominatorChars : List Char := ['1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_meanGapText : String := String.ofList (geometryRow002_meanGapNumeratorChars ++ '/' :: geometryRow002_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_meanGap_before_field"
  err.flush

theorem geometryRow002_meanGap_field :
    geometryRowsJson002.getObjVal? "mean_gap" = .ok (.str geometryRow002_meanGapText) := by rfl

theorem geometryRow002_meanGap_numerator_no_slash :
    geometryRow002_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_meanGap_numerator_parse :
    SourceJson.intChars geometryRow002_meanGapNumeratorChars = some (10824169 : Int) := by decide +kernel

theorem geometryRow002_meanGap_denominator_parse :
    SourceJson.intChars geometryRow002_meanGapDenominatorChars = some (19584000000 : Int) := by decide +kernel

theorem geometryRow002_meanGap_denominator_nonzero : (19584000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_meanGap_parse :
    parseRational geometryRow002_meanGapText = .ok geometryRowsTyped002.meanGap :=
  original_rational_fraction_of_chars geometryRow002_meanGapNumeratorChars geometryRow002_meanGapDenominatorChars
    (10824169 : Int) (19584000000 : Int)
    geometryRow002_meanGap_numerator_no_slash geometryRow002_meanGap_numerator_parse
    geometryRow002_meanGap_denominator_parse geometryRow002_meanGap_denominator_nonzero

theorem geometryRow002_meanGap_read :
    rationalField geometryRowsJson002 "mean_gap" = .ok geometryRowsTyped002.meanGap :=
  original_rationalField_of_string geometryRowsJson002 "mean_gap" geometryRow002_meanGapText
    geometryRowsTyped002.meanGap geometryRow002_meanGap_field geometryRow002_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_meanGap_complete"
  err.flush

noncomputable def geometryRow002_jensenBoundNumeratorChars : List Char := ['5', '8', '3', '1', '0', '2', '8', '3', '8', '8', '2', '2', '9', '5', '8', '5', '4', '2', '2', '2', '7', '8', '9', '4', '0', '9', '3', '4', '4', '4', '5', '3', '0', '4', '4', '0', '6', '3', '8', '9', '7', '8', '7', '5', '9', '1', '2', '9', '4', '7', '7', '2', '1', '4', '1', '0', '9', '9', '7', '2', '5', '1', '4', '8', '2', '1', '0', '4', '5', '4', '6', '4', '6', '7', '2', '7', '1', '0', '6', '1', '6', '7', '8', '4', '8', '4', '7', '4', '7', '2', '1', '9', '5', '5', '4', '8', '7', '1', '3', '3', '1', '7', '9', '0', '2', '6', '4', '4', '4', '2', '6', '4', '2', '0', '6', '6', '8', '6', '5', '2', '7', '3', '9', '7', '5', '5', '3', '6', '5', '4', '3', '4', '2', '3', '6', '4', '3', '6', '3', '4', '7', '5', '2', '7', '2', '3', '7', '7', '9', '7', '3', '6', '1', '0', '4', '7', '6', '9', '2', '1', '9', '2', '8', '4', '8', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_jensenBoundDenominatorChars : List Char := ['3', '4', '2', '2', '5', '3', '5', '3', '5', '6', '3', '6', '4', '8', '9', '0', '8', '4', '7', '4', '4', '0', '4', '3', '3', '7', '6', '0', '1', '8', '1', '1', '4', '5', '1', '7', '1', '3', '5', '0', '4', '7', '4', '1', '1', '0', '6', '2', '3', '4', '2', '4', '5', '5', '3', '6', '3', '5', '7', '5', '1', '9', '7', '9', '3', '0', '8', '6', '9', '1', '4', '5', '1', '8', '4', '2', '4', '9', '3', '9', '4', '3', '8', '8', '1', '3', '8', '2', '6', '7', '3', '6', '1', '8', '5', '8', '2', '1', '4', '3', '2', '6', '4', '3', '5', '7', '5', '8', '4', '6', '7', '9', '5', '5', '1', '6', '2', '5', '6', '3', '3', '0', '9', '9', '1', '2', '6', '3', '3', '2', '8', '8', '2', '2', '7', '0', '7', '1', '8', '0', '5', '3', '5', '9', '5', '2', '4', '4', '7', '6', '8', '4', '6', '6', '1', '8', '7', '2', '8', '6', '6', '5', '1', '5', '5', '0', '8', '1', '7', '4', '3', '9', '6', '0', '6', '2', '7', '3', '7', '1', '1', '4', '8', '1', '9', '2', '2', '3', '2', '9', '7', '9', '4', '9', '9', '0', '8', '4', '1', '6', '9']
noncomputable def geometryRow002_jensenBoundText : String := String.ofList (geometryRow002_jensenBoundNumeratorChars ++ '/' :: geometryRow002_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_jensenBound_before_field"
  err.flush

theorem geometryRow002_jensenBound_field :
    geometryRowsJson002.getObjVal? "jensen_bound" = .ok (.str geometryRow002_jensenBoundText) := by rfl

theorem geometryRow002_jensenBound_numerator_no_slash :
    geometryRow002_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow002_jensenBoundNumeratorChars = some (58310283882295854222789409344453044063897875912947721410997251482104546467271061678484747219554871331790264442642066865273975536543423643634752723779736104769219284820312500000000000000000 : Int) := by decide +kernel

theorem geometryRow002_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow002_jensenBoundDenominatorChars = some (342253535636489084744043376018114517135047411062342455363575197930869145184249394388138267361858214326435758467955162563309912633288227071805359524476846618728665155081743960627371148192232979499084169 : Int) := by decide +kernel

theorem geometryRow002_jensenBound_denominator_nonzero : (342253535636489084744043376018114517135047411062342455363575197930869145184249394388138267361858214326435758467955162563309912633288227071805359524476846618728665155081743960627371148192232979499084169 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_jensenBound_parse :
    parseRational geometryRow002_jensenBoundText = .ok geometryRowsTyped002.jensenBound :=
  original_rational_fraction_of_chars geometryRow002_jensenBoundNumeratorChars geometryRow002_jensenBoundDenominatorChars
    (58310283882295854222789409344453044063897875912947721410997251482104546467271061678484747219554871331790264442642066865273975536543423643634752723779736104769219284820312500000000000000000 : Int) (342253535636489084744043376018114517135047411062342455363575197930869145184249394388138267361858214326435758467955162563309912633288227071805359524476846618728665155081743960627371148192232979499084169 : Int)
    geometryRow002_jensenBound_numerator_no_slash geometryRow002_jensenBound_numerator_parse
    geometryRow002_jensenBound_denominator_parse geometryRow002_jensenBound_denominator_nonzero

theorem geometryRow002_jensenBound_read :
    rationalField geometryRowsJson002 "jensen_bound" = .ok geometryRowsTyped002.jensenBound :=
  original_rationalField_of_string geometryRowsJson002 "jensen_bound" geometryRow002_jensenBoundText
    geometryRowsTyped002.jensenBound geometryRow002_jensenBound_field geometryRow002_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_factorMaxima_before"
  err.flush

theorem geometryRow002_factorMaxima_read :
    rationalArrayField geometryRowsJson002 "factor_maxima" = .ok geometryRowsTyped002.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_gapWeightedMeans_before"
  err.flush

theorem geometryRow002_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson002 "gap_weighted_means" = .ok geometryRowsTyped002.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow002_floorChars : List Char := ['1', '3', '4', '9', '8', '2', '2', '9', '1', '3', '9', '0', '7', '3', '6', '0', '7']
noncomputable def geometryRow002_floorText : String := String.ofList geometryRow002_floorChars

theorem geometryRow002_floor_text_read :
    geometryRowsJson002.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow002_floorText := by rfl

theorem geometryRow002_floor_chars_parse :
    SourceJson.intChars geometryRow002_floorChars = some (13498229139073607 : Int) := by decide +kernel

theorem geometryRow002_floor_parse :
    parseInteger geometryRow002_floorText = .ok geometryRowsTyped002.jensenFloorQ96 := by
  simp only [geometryRow002_floorText, parseInteger, String.toList_ofList, geometryRow002_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_002 :
    decodeGeometryRow geometryRowsJson002 = .ok geometryRowsTyped002 :=
  original_geometryRow_of_fields geometryRowsJson002 geometryRowsTyped002 geometryRow002_floorText
    geometryRow002_simplexId_read geometryRow002_vertexIds_read
    geometryRow002_physicalVolume_read geometryRow002_meanGap_read
    geometryRow002_factorMaxima_read geometryRow002_gapWeightedMeans_read
    geometryRow002_jensenBound_read geometryRow002_floor_text_read geometryRow002_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_002_original_decoder_complete"
  err.flush

theorem geometryRow002_shape :
    geometryRowsTyped002.simplexId = 2 ∧
    geometryRowsTyped002.vertexIds.size = 9 ∧ geometryRowsTyped002.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped002.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped002.factorMaxima.size = 10 ∧ geometryRowsTyped002.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson003 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped003 : GeometryRow :=
  { simplexId := 3,
    vertexIds := #[27, 13, 11, 9, 7, 6, 4, 2, 0],
    physicalVolume := ((7099426585687109899171081712133327277386847 : ℚ) / (41637198415527936000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((16828009 : ℚ) / (180000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((88729506324609 : ℚ) / (941449600000000 : ℚ)), ((2787875390117 : ℚ) / (29420300000000 : ℚ)), ((99597459470689 : ℚ) / (847304640000000 : ℚ)), ((30388354819447 : ℚ) / (353043600000000 : ℚ)), ((223795124701 : ℚ) / (2758153125000 : ℚ)), ((3226576483849 : ℚ) / (42365232000000 : ℚ)), ((171577508984849 : ℚ) / (4236523200000000 : ℚ)), ((146255077808701 : ℚ) / (4236523200000000 : ℚ)), ((144736124503741 : ℚ) / (4236523200000000 : ℚ)), ((17209758499837 : ℚ) / (529565400000000 : ℚ))],
    jensenBound := ((229408516436020857048663540653638875225428412098054979433595161269757188913443009356700812825606559375000000000000000000 : ℚ) / (1023996672770626060260591527598708049108676484891576705682304474648332571583188129792566770821037545928136289779235870087781218978251 : ℚ)),
    jensenFloorQ96 := (17749681913683967 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_simplexId_before"
  err.flush

theorem geometryRow003_simplexId_read :
    geometryRowsJson003.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped003.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_vertexIds_before"
  err.flush

theorem geometryRow003_vertexIds_read :
    geometryRowsJson003.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped003.vertexIds := by decide +kernel

noncomputable def geometryRow003_physicalVolumeNumeratorChars : List Char := ['7', '0', '9', '9', '4', '2', '6', '5', '8', '5', '6', '8', '7', '1', '0', '9', '8', '9', '9', '1', '7', '1', '0', '8', '1', '7', '1', '2', '1', '3', '3', '3', '2', '7', '2', '7', '7', '3', '8', '6', '8', '4', '7']
noncomputable def geometryRow003_physicalVolumeDenominatorChars : List Char := ['4', '1', '6', '3', '7', '1', '9', '8', '4', '1', '5', '5', '2', '7', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_physicalVolumeText : String := String.ofList (geometryRow003_physicalVolumeNumeratorChars ++ '/' :: geometryRow003_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_physicalVolume_before_field"
  err.flush

theorem geometryRow003_physicalVolume_field :
    geometryRowsJson003.getObjVal? "physical_volume" = .ok (.str geometryRow003_physicalVolumeText) := by rfl

theorem geometryRow003_physicalVolume_numerator_no_slash :
    geometryRow003_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow003_physicalVolumeNumeratorChars = some (7099426585687109899171081712133327277386847 : Int) := by decide +kernel

theorem geometryRow003_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow003_physicalVolumeDenominatorChars = some (41637198415527936000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow003_physicalVolume_denominator_nonzero : (41637198415527936000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_physicalVolume_parse :
    parseRational geometryRow003_physicalVolumeText = .ok geometryRowsTyped003.physicalVolume :=
  original_rational_fraction_of_chars geometryRow003_physicalVolumeNumeratorChars geometryRow003_physicalVolumeDenominatorChars
    (7099426585687109899171081712133327277386847 : Int) (41637198415527936000000000000000000000000000000000000000000000000 : Int)
    geometryRow003_physicalVolume_numerator_no_slash geometryRow003_physicalVolume_numerator_parse
    geometryRow003_physicalVolume_denominator_parse geometryRow003_physicalVolume_denominator_nonzero

theorem geometryRow003_physicalVolume_read :
    rationalField geometryRowsJson003 "physical_volume" = .ok geometryRowsTyped003.physicalVolume :=
  original_rationalField_of_string geometryRowsJson003 "physical_volume" geometryRow003_physicalVolumeText
    geometryRowsTyped003.physicalVolume geometryRow003_physicalVolume_field geometryRow003_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_physicalVolume_complete"
  err.flush

noncomputable def geometryRow003_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow003_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_meanGapText : String := String.ofList (geometryRow003_meanGapNumeratorChars ++ '/' :: geometryRow003_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_meanGap_before_field"
  err.flush

theorem geometryRow003_meanGap_field :
    geometryRowsJson003.getObjVal? "mean_gap" = .ok (.str geometryRow003_meanGapText) := by rfl

theorem geometryRow003_meanGap_numerator_no_slash :
    geometryRow003_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_meanGap_numerator_parse :
    SourceJson.intChars geometryRow003_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow003_meanGap_denominator_parse :
    SourceJson.intChars geometryRow003_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow003_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_meanGap_parse :
    parseRational geometryRow003_meanGapText = .ok geometryRowsTyped003.meanGap :=
  original_rational_fraction_of_chars geometryRow003_meanGapNumeratorChars geometryRow003_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow003_meanGap_numerator_no_slash geometryRow003_meanGap_numerator_parse
    geometryRow003_meanGap_denominator_parse geometryRow003_meanGap_denominator_nonzero

theorem geometryRow003_meanGap_read :
    rationalField geometryRowsJson003 "mean_gap" = .ok geometryRowsTyped003.meanGap :=
  original_rationalField_of_string geometryRowsJson003 "mean_gap" geometryRow003_meanGapText
    geometryRowsTyped003.meanGap geometryRow003_meanGap_field geometryRow003_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_meanGap_complete"
  err.flush

noncomputable def geometryRow003_jensenBoundNumeratorChars : List Char := ['2', '2', '9', '4', '0', '8', '5', '1', '6', '4', '3', '6', '0', '2', '0', '8', '5', '7', '0', '4', '8', '6', '6', '3', '5', '4', '0', '6', '5', '3', '6', '3', '8', '8', '7', '5', '2', '2', '5', '4', '2', '8', '4', '1', '2', '0', '9', '8', '0', '5', '4', '9', '7', '9', '4', '3', '3', '5', '9', '5', '1', '6', '1', '2', '6', '9', '7', '5', '7', '1', '8', '8', '9', '1', '3', '4', '4', '3', '0', '0', '9', '3', '5', '6', '7', '0', '0', '8', '1', '2', '8', '2', '5', '6', '0', '6', '5', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_jensenBoundDenominatorChars : List Char := ['1', '0', '2', '3', '9', '9', '6', '6', '7', '2', '7', '7', '0', '6', '2', '6', '0', '6', '0', '2', '6', '0', '5', '9', '1', '5', '2', '7', '5', '9', '8', '7', '0', '8', '0', '4', '9', '1', '0', '8', '6', '7', '6', '4', '8', '4', '8', '9', '1', '5', '7', '6', '7', '0', '5', '6', '8', '2', '3', '0', '4', '4', '7', '4', '6', '4', '8', '3', '3', '2', '5', '7', '1', '5', '8', '3', '1', '8', '8', '1', '2', '9', '7', '9', '2', '5', '6', '6', '7', '7', '0', '8', '2', '1', '0', '3', '7', '5', '4', '5', '9', '2', '8', '1', '3', '6', '2', '8', '9', '7', '7', '9', '2', '3', '5', '8', '7', '0', '0', '8', '7', '7', '8', '1', '2', '1', '8', '9', '7', '8', '2', '5', '1']
noncomputable def geometryRow003_jensenBoundText : String := String.ofList (geometryRow003_jensenBoundNumeratorChars ++ '/' :: geometryRow003_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_jensenBound_before_field"
  err.flush

theorem geometryRow003_jensenBound_field :
    geometryRowsJson003.getObjVal? "jensen_bound" = .ok (.str geometryRow003_jensenBoundText) := by rfl

theorem geometryRow003_jensenBound_numerator_no_slash :
    geometryRow003_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow003_jensenBoundNumeratorChars = some (229408516436020857048663540653638875225428412098054979433595161269757188913443009356700812825606559375000000000000000000 : Int) := by decide +kernel

theorem geometryRow003_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow003_jensenBoundDenominatorChars = some (1023996672770626060260591527598708049108676484891576705682304474648332571583188129792566770821037545928136289779235870087781218978251 : Int) := by decide +kernel

theorem geometryRow003_jensenBound_denominator_nonzero : (1023996672770626060260591527598708049108676484891576705682304474648332571583188129792566770821037545928136289779235870087781218978251 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_jensenBound_parse :
    parseRational geometryRow003_jensenBoundText = .ok geometryRowsTyped003.jensenBound :=
  original_rational_fraction_of_chars geometryRow003_jensenBoundNumeratorChars geometryRow003_jensenBoundDenominatorChars
    (229408516436020857048663540653638875225428412098054979433595161269757188913443009356700812825606559375000000000000000000 : Int) (1023996672770626060260591527598708049108676484891576705682304474648332571583188129792566770821037545928136289779235870087781218978251 : Int)
    geometryRow003_jensenBound_numerator_no_slash geometryRow003_jensenBound_numerator_parse
    geometryRow003_jensenBound_denominator_parse geometryRow003_jensenBound_denominator_nonzero

theorem geometryRow003_jensenBound_read :
    rationalField geometryRowsJson003 "jensen_bound" = .ok geometryRowsTyped003.jensenBound :=
  original_rationalField_of_string geometryRowsJson003 "jensen_bound" geometryRow003_jensenBoundText
    geometryRowsTyped003.jensenBound geometryRow003_jensenBound_field geometryRow003_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_factorMaxima_before"
  err.flush

theorem geometryRow003_factorMaxima_read :
    rationalArrayField geometryRowsJson003 "factor_maxima" = .ok geometryRowsTyped003.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_gapWeightedMeans_before"
  err.flush

theorem geometryRow003_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson003 "gap_weighted_means" = .ok geometryRowsTyped003.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow003_floorChars : List Char := ['1', '7', '7', '4', '9', '6', '8', '1', '9', '1', '3', '6', '8', '3', '9', '6', '7']
noncomputable def geometryRow003_floorText : String := String.ofList geometryRow003_floorChars

theorem geometryRow003_floor_text_read :
    geometryRowsJson003.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow003_floorText := by rfl

theorem geometryRow003_floor_chars_parse :
    SourceJson.intChars geometryRow003_floorChars = some (17749681913683967 : Int) := by decide +kernel

theorem geometryRow003_floor_parse :
    parseInteger geometryRow003_floorText = .ok geometryRowsTyped003.jensenFloorQ96 := by
  simp only [geometryRow003_floorText, parseInteger, String.toList_ofList, geometryRow003_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_003 :
    decodeGeometryRow geometryRowsJson003 = .ok geometryRowsTyped003 :=
  original_geometryRow_of_fields geometryRowsJson003 geometryRowsTyped003 geometryRow003_floorText
    geometryRow003_simplexId_read geometryRow003_vertexIds_read
    geometryRow003_physicalVolume_read geometryRow003_meanGap_read
    geometryRow003_factorMaxima_read geometryRow003_gapWeightedMeans_read
    geometryRow003_jensenBound_read geometryRow003_floor_text_read geometryRow003_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_003_original_decoder_complete"
  err.flush

theorem geometryRow003_shape :
    geometryRowsTyped003.simplexId = 3 ∧
    geometryRowsTyped003.vertexIds.size = 9 ∧ geometryRowsTyped003.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped003.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped003.factorMaxima.size = 10 ∧ geometryRowsTyped003.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson004 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped004 : GeometryRow :=
  { simplexId := 4,
    vertexIds := #[27, 13, 11, 9, 8, 7, 5, 3, 1],
    physicalVolume := ((908812444379187905021525072020199385557 : ℚ) / (35057735458357248000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((16828009 : ℚ) / (180000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((10639165753441 : ℚ) / (113240400000000 : ℚ)), ((10693787759971 : ℚ) / (113240400000000 : ℚ)), ((5329976099659 : ℚ) / (45296160000000 : ℚ)), ((57980775024703 : ℚ) / (679442400000000 : ℚ)), ((54962108446447 : ℚ) / (679442400000000 : ℚ)), ((3460963931669 : ℚ) / (45296160000000 : ℚ)), ((13716695933089 : ℚ) / (339721200000000 : ℚ)), ((1317069741649 : ℚ) / (37746800000000 : ℚ)), ((1291385284669 : ℚ) / (37746800000000 : ℚ)), ((11312844716671 : ℚ) / (339721200000000 : ℚ))],
    jensenBound := ((166495244161643560237999160025466171631469571195773406381463017521712159375248854585820592000000000000000000000000 : ℚ) / (5295610920685334983692878555680207697351058797167929344851832028706095961940656184183142401263565743620358867905496316683358000157 : ℚ)),
    jensenFloorQ96 := (2490951933565 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_simplexId_before"
  err.flush

theorem geometryRow004_simplexId_read :
    geometryRowsJson004.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped004.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_vertexIds_before"
  err.flush

theorem geometryRow004_vertexIds_read :
    geometryRowsJson004.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped004.vertexIds := by decide +kernel

noncomputable def geometryRow004_physicalVolumeNumeratorChars : List Char := ['9', '0', '8', '8', '1', '2', '4', '4', '4', '3', '7', '9', '1', '8', '7', '9', '0', '5', '0', '2', '1', '5', '2', '5', '0', '7', '2', '0', '2', '0', '1', '9', '9', '3', '8', '5', '5', '5', '7']
noncomputable def geometryRow004_physicalVolumeDenominatorChars : List Char := ['3', '5', '0', '5', '7', '7', '3', '5', '4', '5', '8', '3', '5', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_physicalVolumeText : String := String.ofList (geometryRow004_physicalVolumeNumeratorChars ++ '/' :: geometryRow004_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_physicalVolume_before_field"
  err.flush

theorem geometryRow004_physicalVolume_field :
    geometryRowsJson004.getObjVal? "physical_volume" = .ok (.str geometryRow004_physicalVolumeText) := by rfl

theorem geometryRow004_physicalVolume_numerator_no_slash :
    geometryRow004_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow004_physicalVolumeNumeratorChars = some (908812444379187905021525072020199385557 : Int) := by decide +kernel

theorem geometryRow004_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow004_physicalVolumeDenominatorChars = some (35057735458357248000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow004_physicalVolume_denominator_nonzero : (35057735458357248000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_physicalVolume_parse :
    parseRational geometryRow004_physicalVolumeText = .ok geometryRowsTyped004.physicalVolume :=
  original_rational_fraction_of_chars geometryRow004_physicalVolumeNumeratorChars geometryRow004_physicalVolumeDenominatorChars
    (908812444379187905021525072020199385557 : Int) (35057735458357248000000000000000000000000000000000000000000000000 : Int)
    geometryRow004_physicalVolume_numerator_no_slash geometryRow004_physicalVolume_numerator_parse
    geometryRow004_physicalVolume_denominator_parse geometryRow004_physicalVolume_denominator_nonzero

theorem geometryRow004_physicalVolume_read :
    rationalField geometryRowsJson004 "physical_volume" = .ok geometryRowsTyped004.physicalVolume :=
  original_rationalField_of_string geometryRowsJson004 "physical_volume" geometryRow004_physicalVolumeText
    geometryRowsTyped004.physicalVolume geometryRow004_physicalVolume_field geometryRow004_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_physicalVolume_complete"
  err.flush

noncomputable def geometryRow004_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow004_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_meanGapText : String := String.ofList (geometryRow004_meanGapNumeratorChars ++ '/' :: geometryRow004_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_meanGap_before_field"
  err.flush

theorem geometryRow004_meanGap_field :
    geometryRowsJson004.getObjVal? "mean_gap" = .ok (.str geometryRow004_meanGapText) := by rfl

theorem geometryRow004_meanGap_numerator_no_slash :
    geometryRow004_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_meanGap_numerator_parse :
    SourceJson.intChars geometryRow004_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow004_meanGap_denominator_parse :
    SourceJson.intChars geometryRow004_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow004_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_meanGap_parse :
    parseRational geometryRow004_meanGapText = .ok geometryRowsTyped004.meanGap :=
  original_rational_fraction_of_chars geometryRow004_meanGapNumeratorChars geometryRow004_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow004_meanGap_numerator_no_slash geometryRow004_meanGap_numerator_parse
    geometryRow004_meanGap_denominator_parse geometryRow004_meanGap_denominator_nonzero

theorem geometryRow004_meanGap_read :
    rationalField geometryRowsJson004 "mean_gap" = .ok geometryRowsTyped004.meanGap :=
  original_rationalField_of_string geometryRowsJson004 "mean_gap" geometryRow004_meanGapText
    geometryRowsTyped004.meanGap geometryRow004_meanGap_field geometryRow004_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_meanGap_complete"
  err.flush

noncomputable def geometryRow004_jensenBoundNumeratorChars : List Char := ['1', '6', '6', '4', '9', '5', '2', '4', '4', '1', '6', '1', '6', '4', '3', '5', '6', '0', '2', '3', '7', '9', '9', '9', '1', '6', '0', '0', '2', '5', '4', '6', '6', '1', '7', '1', '6', '3', '1', '4', '6', '9', '5', '7', '1', '1', '9', '5', '7', '7', '3', '4', '0', '6', '3', '8', '1', '4', '6', '3', '0', '1', '7', '5', '2', '1', '7', '1', '2', '1', '5', '9', '3', '7', '5', '2', '4', '8', '8', '5', '4', '5', '8', '5', '8', '2', '0', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_jensenBoundDenominatorChars : List Char := ['5', '2', '9', '5', '6', '1', '0', '9', '2', '0', '6', '8', '5', '3', '3', '4', '9', '8', '3', '6', '9', '2', '8', '7', '8', '5', '5', '5', '6', '8', '0', '2', '0', '7', '6', '9', '7', '3', '5', '1', '0', '5', '8', '7', '9', '7', '1', '6', '7', '9', '2', '9', '3', '4', '4', '8', '5', '1', '8', '3', '2', '0', '2', '8', '7', '0', '6', '0', '9', '5', '9', '6', '1', '9', '4', '0', '6', '5', '6', '1', '8', '4', '1', '8', '3', '1', '4', '2', '4', '0', '1', '2', '6', '3', '5', '6', '5', '7', '4', '3', '6', '2', '0', '3', '5', '8', '8', '6', '7', '9', '0', '5', '4', '9', '6', '3', '1', '6', '6', '8', '3', '3', '5', '8', '0', '0', '0', '1', '5', '7']
noncomputable def geometryRow004_jensenBoundText : String := String.ofList (geometryRow004_jensenBoundNumeratorChars ++ '/' :: geometryRow004_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_jensenBound_before_field"
  err.flush

theorem geometryRow004_jensenBound_field :
    geometryRowsJson004.getObjVal? "jensen_bound" = .ok (.str geometryRow004_jensenBoundText) := by rfl

theorem geometryRow004_jensenBound_numerator_no_slash :
    geometryRow004_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow004_jensenBoundNumeratorChars = some (166495244161643560237999160025466171631469571195773406381463017521712159375248854585820592000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow004_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow004_jensenBoundDenominatorChars = some (5295610920685334983692878555680207697351058797167929344851832028706095961940656184183142401263565743620358867905496316683358000157 : Int) := by decide +kernel

theorem geometryRow004_jensenBound_denominator_nonzero : (5295610920685334983692878555680207697351058797167929344851832028706095961940656184183142401263565743620358867905496316683358000157 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_jensenBound_parse :
    parseRational geometryRow004_jensenBoundText = .ok geometryRowsTyped004.jensenBound :=
  original_rational_fraction_of_chars geometryRow004_jensenBoundNumeratorChars geometryRow004_jensenBoundDenominatorChars
    (166495244161643560237999160025466171631469571195773406381463017521712159375248854585820592000000000000000000000000 : Int) (5295610920685334983692878555680207697351058797167929344851832028706095961940656184183142401263565743620358867905496316683358000157 : Int)
    geometryRow004_jensenBound_numerator_no_slash geometryRow004_jensenBound_numerator_parse
    geometryRow004_jensenBound_denominator_parse geometryRow004_jensenBound_denominator_nonzero

theorem geometryRow004_jensenBound_read :
    rationalField geometryRowsJson004 "jensen_bound" = .ok geometryRowsTyped004.jensenBound :=
  original_rationalField_of_string geometryRowsJson004 "jensen_bound" geometryRow004_jensenBoundText
    geometryRowsTyped004.jensenBound geometryRow004_jensenBound_field geometryRow004_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_factorMaxima_before"
  err.flush

theorem geometryRow004_factorMaxima_read :
    rationalArrayField geometryRowsJson004 "factor_maxima" = .ok geometryRowsTyped004.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_gapWeightedMeans_before"
  err.flush

theorem geometryRow004_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson004 "gap_weighted_means" = .ok geometryRowsTyped004.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow004_floorChars : List Char := ['2', '4', '9', '0', '9', '5', '1', '9', '3', '3', '5', '6', '5']
noncomputable def geometryRow004_floorText : String := String.ofList geometryRow004_floorChars

theorem geometryRow004_floor_text_read :
    geometryRowsJson004.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow004_floorText := by rfl

theorem geometryRow004_floor_chars_parse :
    SourceJson.intChars geometryRow004_floorChars = some (2490951933565 : Int) := by decide +kernel

theorem geometryRow004_floor_parse :
    parseInteger geometryRow004_floorText = .ok geometryRowsTyped004.jensenFloorQ96 := by
  simp only [geometryRow004_floorText, parseInteger, String.toList_ofList, geometryRow004_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_004 :
    decodeGeometryRow geometryRowsJson004 = .ok geometryRowsTyped004 :=
  original_geometryRow_of_fields geometryRowsJson004 geometryRowsTyped004 geometryRow004_floorText
    geometryRow004_simplexId_read geometryRow004_vertexIds_read
    geometryRow004_physicalVolume_read geometryRow004_meanGap_read
    geometryRow004_factorMaxima_read geometryRow004_gapWeightedMeans_read
    geometryRow004_jensenBound_read geometryRow004_floor_text_read geometryRow004_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_004_original_decoder_complete"
  err.flush

theorem geometryRow004_shape :
    geometryRowsTyped004.simplexId = 4 ∧
    geometryRowsTyped004.vertexIds.size = 9 ∧ geometryRowsTyped004.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped004.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped004.factorMaxima.size = 10 ∧ geometryRowsTyped004.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson005 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped005 : GeometryRow :=
  { simplexId := 5,
    vertexIds := #[27, 13, 11, 10, 8, 7, 5, 3, 1],
    physicalVolume := ((298113201535509937050098485899882708510981709 : ℚ) / (1121847534667431936000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((16828009 : ℚ) / (180000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((7144369652479 : ℚ) / (75493600000000 : ℚ)), ((7180784323499 : ℚ) / (75493600000000 : ℚ)), ((5329976099659 : ℚ) / (45296160000000 : ℚ)), ((3652816380013 : ℚ) / (42465150000000 : ℚ)), ((54962108446447 : ℚ) / (679442400000000 : ℚ)), ((3460963931669 : ℚ) / (45296160000000 : ℚ)), ((13716695933089 : ℚ) / (339721200000000 : ℚ)), ((1317069741649 : ℚ) / (37746800000000 : ℚ)), ((7593534257459 : ℚ) / (226480800000000 : ℚ)), ((22161402377837 : ℚ) / (679442400000000 : ℚ))],
    jensenBound := ((1706706324020786633423445820719317999695362794925459101982701481058404901470369982833024002609500000000000000000000000 : ℚ) / (5198659224393294929090766966347473338323865251693161271597017856937364830095481810884577482369097209686011038219331698396721995367 : ℚ)),
    jensenFloorQ96 := (26010400021829131 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_simplexId_before"
  err.flush

theorem geometryRow005_simplexId_read :
    geometryRowsJson005.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped005.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_vertexIds_before"
  err.flush

theorem geometryRow005_vertexIds_read :
    geometryRowsJson005.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped005.vertexIds := by decide +kernel

noncomputable def geometryRow005_physicalVolumeNumeratorChars : List Char := ['2', '9', '8', '1', '1', '3', '2', '0', '1', '5', '3', '5', '5', '0', '9', '9', '3', '7', '0', '5', '0', '0', '9', '8', '4', '8', '5', '8', '9', '9', '8', '8', '2', '7', '0', '8', '5', '1', '0', '9', '8', '1', '7', '0', '9']
noncomputable def geometryRow005_physicalVolumeDenominatorChars : List Char := ['1', '1', '2', '1', '8', '4', '7', '5', '3', '4', '6', '6', '7', '4', '3', '1', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_physicalVolumeText : String := String.ofList (geometryRow005_physicalVolumeNumeratorChars ++ '/' :: geometryRow005_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_physicalVolume_before_field"
  err.flush

theorem geometryRow005_physicalVolume_field :
    geometryRowsJson005.getObjVal? "physical_volume" = .ok (.str geometryRow005_physicalVolumeText) := by rfl

theorem geometryRow005_physicalVolume_numerator_no_slash :
    geometryRow005_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow005_physicalVolumeNumeratorChars = some (298113201535509937050098485899882708510981709 : Int) := by decide +kernel

theorem geometryRow005_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow005_physicalVolumeDenominatorChars = some (1121847534667431936000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow005_physicalVolume_denominator_nonzero : (1121847534667431936000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_physicalVolume_parse :
    parseRational geometryRow005_physicalVolumeText = .ok geometryRowsTyped005.physicalVolume :=
  original_rational_fraction_of_chars geometryRow005_physicalVolumeNumeratorChars geometryRow005_physicalVolumeDenominatorChars
    (298113201535509937050098485899882708510981709 : Int) (1121847534667431936000000000000000000000000000000000000000000000000 : Int)
    geometryRow005_physicalVolume_numerator_no_slash geometryRow005_physicalVolume_numerator_parse
    geometryRow005_physicalVolume_denominator_parse geometryRow005_physicalVolume_denominator_nonzero

theorem geometryRow005_physicalVolume_read :
    rationalField geometryRowsJson005 "physical_volume" = .ok geometryRowsTyped005.physicalVolume :=
  original_rationalField_of_string geometryRowsJson005 "physical_volume" geometryRow005_physicalVolumeText
    geometryRowsTyped005.physicalVolume geometryRow005_physicalVolume_field geometryRow005_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_physicalVolume_complete"
  err.flush

noncomputable def geometryRow005_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow005_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_meanGapText : String := String.ofList (geometryRow005_meanGapNumeratorChars ++ '/' :: geometryRow005_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_meanGap_before_field"
  err.flush

theorem geometryRow005_meanGap_field :
    geometryRowsJson005.getObjVal? "mean_gap" = .ok (.str geometryRow005_meanGapText) := by rfl

theorem geometryRow005_meanGap_numerator_no_slash :
    geometryRow005_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_meanGap_numerator_parse :
    SourceJson.intChars geometryRow005_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow005_meanGap_denominator_parse :
    SourceJson.intChars geometryRow005_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow005_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_meanGap_parse :
    parseRational geometryRow005_meanGapText = .ok geometryRowsTyped005.meanGap :=
  original_rational_fraction_of_chars geometryRow005_meanGapNumeratorChars geometryRow005_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow005_meanGap_numerator_no_slash geometryRow005_meanGap_numerator_parse
    geometryRow005_meanGap_denominator_parse geometryRow005_meanGap_denominator_nonzero

theorem geometryRow005_meanGap_read :
    rationalField geometryRowsJson005 "mean_gap" = .ok geometryRowsTyped005.meanGap :=
  original_rationalField_of_string geometryRowsJson005 "mean_gap" geometryRow005_meanGapText
    geometryRowsTyped005.meanGap geometryRow005_meanGap_field geometryRow005_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_meanGap_complete"
  err.flush

noncomputable def geometryRow005_jensenBoundNumeratorChars : List Char := ['1', '7', '0', '6', '7', '0', '6', '3', '2', '4', '0', '2', '0', '7', '8', '6', '6', '3', '3', '4', '2', '3', '4', '4', '5', '8', '2', '0', '7', '1', '9', '3', '1', '7', '9', '9', '9', '6', '9', '5', '3', '6', '2', '7', '9', '4', '9', '2', '5', '4', '5', '9', '1', '0', '1', '9', '8', '2', '7', '0', '1', '4', '8', '1', '0', '5', '8', '4', '0', '4', '9', '0', '1', '4', '7', '0', '3', '6', '9', '9', '8', '2', '8', '3', '3', '0', '2', '4', '0', '0', '2', '6', '0', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_jensenBoundDenominatorChars : List Char := ['5', '1', '9', '8', '6', '5', '9', '2', '2', '4', '3', '9', '3', '2', '9', '4', '9', '2', '9', '0', '9', '0', '7', '6', '6', '9', '6', '6', '3', '4', '7', '4', '7', '3', '3', '3', '8', '3', '2', '3', '8', '6', '5', '2', '5', '1', '6', '9', '3', '1', '6', '1', '2', '7', '1', '5', '9', '7', '0', '1', '7', '8', '5', '6', '9', '3', '7', '3', '6', '4', '8', '3', '0', '0', '9', '5', '4', '8', '1', '8', '1', '0', '8', '8', '4', '5', '7', '7', '4', '8', '2', '3', '6', '9', '0', '9', '7', '2', '0', '9', '6', '8', '6', '0', '1', '1', '0', '3', '8', '2', '1', '9', '3', '3', '1', '6', '9', '8', '3', '9', '6', '7', '2', '1', '9', '9', '5', '3', '6', '7']
noncomputable def geometryRow005_jensenBoundText : String := String.ofList (geometryRow005_jensenBoundNumeratorChars ++ '/' :: geometryRow005_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_jensenBound_before_field"
  err.flush

theorem geometryRow005_jensenBound_field :
    geometryRowsJson005.getObjVal? "jensen_bound" = .ok (.str geometryRow005_jensenBoundText) := by rfl

theorem geometryRow005_jensenBound_numerator_no_slash :
    geometryRow005_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow005_jensenBoundNumeratorChars = some (1706706324020786633423445820719317999695362794925459101982701481058404901470369982833024002609500000000000000000000000 : Int) := by decide +kernel

theorem geometryRow005_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow005_jensenBoundDenominatorChars = some (5198659224393294929090766966347473338323865251693161271597017856937364830095481810884577482369097209686011038219331698396721995367 : Int) := by decide +kernel

theorem geometryRow005_jensenBound_denominator_nonzero : (5198659224393294929090766966347473338323865251693161271597017856937364830095481810884577482369097209686011038219331698396721995367 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_jensenBound_parse :
    parseRational geometryRow005_jensenBoundText = .ok geometryRowsTyped005.jensenBound :=
  original_rational_fraction_of_chars geometryRow005_jensenBoundNumeratorChars geometryRow005_jensenBoundDenominatorChars
    (1706706324020786633423445820719317999695362794925459101982701481058404901470369982833024002609500000000000000000000000 : Int) (5198659224393294929090766966347473338323865251693161271597017856937364830095481810884577482369097209686011038219331698396721995367 : Int)
    geometryRow005_jensenBound_numerator_no_slash geometryRow005_jensenBound_numerator_parse
    geometryRow005_jensenBound_denominator_parse geometryRow005_jensenBound_denominator_nonzero

theorem geometryRow005_jensenBound_read :
    rationalField geometryRowsJson005 "jensen_bound" = .ok geometryRowsTyped005.jensenBound :=
  original_rationalField_of_string geometryRowsJson005 "jensen_bound" geometryRow005_jensenBoundText
    geometryRowsTyped005.jensenBound geometryRow005_jensenBound_field geometryRow005_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_factorMaxima_before"
  err.flush

theorem geometryRow005_factorMaxima_read :
    rationalArrayField geometryRowsJson005 "factor_maxima" = .ok geometryRowsTyped005.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_gapWeightedMeans_before"
  err.flush

theorem geometryRow005_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson005 "gap_weighted_means" = .ok geometryRowsTyped005.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow005_floorChars : List Char := ['2', '6', '0', '1', '0', '4', '0', '0', '0', '2', '1', '8', '2', '9', '1', '3', '1']
noncomputable def geometryRow005_floorText : String := String.ofList geometryRow005_floorChars

theorem geometryRow005_floor_text_read :
    geometryRowsJson005.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow005_floorText := by rfl

theorem geometryRow005_floor_chars_parse :
    SourceJson.intChars geometryRow005_floorChars = some (26010400021829131 : Int) := by decide +kernel

theorem geometryRow005_floor_parse :
    parseInteger geometryRow005_floorText = .ok geometryRowsTyped005.jensenFloorQ96 := by
  simp only [geometryRow005_floorText, parseInteger, String.toList_ofList, geometryRow005_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_005 :
    decodeGeometryRow geometryRowsJson005 = .ok geometryRowsTyped005 :=
  original_geometryRow_of_fields geometryRowsJson005 geometryRowsTyped005 geometryRow005_floorText
    geometryRow005_simplexId_read geometryRow005_vertexIds_read
    geometryRow005_physicalVolume_read geometryRow005_meanGap_read
    geometryRow005_factorMaxima_read geometryRow005_gapWeightedMeans_read
    geometryRow005_jensenBound_read geometryRow005_floor_text_read geometryRow005_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_005_original_decoder_complete"
  err.flush

theorem geometryRow005_shape :
    geometryRowsTyped005.simplexId = 5 ∧
    geometryRowsTyped005.vertexIds.size = 9 ∧ geometryRowsTyped005.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped005.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped005.factorMaxima.size = 10 ∧ geometryRowsTyped005.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson006 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped006 : GeometryRow :=
  { simplexId := 6,
    vertexIds := #[27, 13, 12, 10, 8, 7, 5, 3, 1],
    physicalVolume := ((908768113821838334811709937522961225797 : ℚ) / (46743647277809664000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((16828009 : ℚ) / (180000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((21623600796877 : ℚ) / (226480800000000 : ℚ)), ((21732844809937 : ℚ) / (226480800000000 : ℚ)), ((1067899987339 : ℚ) / (9059232000000 : ℚ)), ((4866452316359 : ℚ) / (56620200000000 : ℚ)), ((54819250890907 : ℚ) / (679442400000000 : ℚ)), ((3451440094633 : ℚ) / (45296160000000 : ℚ)), ((13859553488629 : ℚ) / (339721200000000 : ℚ)), ((1293260149059 : ℚ) / (37746800000000 : ℚ)), ((2483553867733 : ℚ) / (75493600000000 : ℚ)), ((7450631405759 : ℚ) / (226480800000000 : ℚ))],
    jensenBound := ((33297424552860404305358609811932709784370346311539175449994473209919541456060079400536406400000000000000000000000 : ℚ) / (1379321134021080022615353157587757663508719746829304263138415356827446160625030906189891988144830575158196049062204504806222762607 : ℚ)),
    jensenFloorQ96 := (1912603018043 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_simplexId_before"
  err.flush

theorem geometryRow006_simplexId_read :
    geometryRowsJson006.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped006.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_vertexIds_before"
  err.flush

theorem geometryRow006_vertexIds_read :
    geometryRowsJson006.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped006.vertexIds := by decide +kernel

noncomputable def geometryRow006_physicalVolumeNumeratorChars : List Char := ['9', '0', '8', '7', '6', '8', '1', '1', '3', '8', '2', '1', '8', '3', '8', '3', '3', '4', '8', '1', '1', '7', '0', '9', '9', '3', '7', '5', '2', '2', '9', '6', '1', '2', '2', '5', '7', '9', '7']
noncomputable def geometryRow006_physicalVolumeDenominatorChars : List Char := ['4', '6', '7', '4', '3', '6', '4', '7', '2', '7', '7', '8', '0', '9', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_physicalVolumeText : String := String.ofList (geometryRow006_physicalVolumeNumeratorChars ++ '/' :: geometryRow006_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_physicalVolume_before_field"
  err.flush

theorem geometryRow006_physicalVolume_field :
    geometryRowsJson006.getObjVal? "physical_volume" = .ok (.str geometryRow006_physicalVolumeText) := by rfl

theorem geometryRow006_physicalVolume_numerator_no_slash :
    geometryRow006_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow006_physicalVolumeNumeratorChars = some (908768113821838334811709937522961225797 : Int) := by decide +kernel

theorem geometryRow006_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow006_physicalVolumeDenominatorChars = some (46743647277809664000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow006_physicalVolume_denominator_nonzero : (46743647277809664000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_physicalVolume_parse :
    parseRational geometryRow006_physicalVolumeText = .ok geometryRowsTyped006.physicalVolume :=
  original_rational_fraction_of_chars geometryRow006_physicalVolumeNumeratorChars geometryRow006_physicalVolumeDenominatorChars
    (908768113821838334811709937522961225797 : Int) (46743647277809664000000000000000000000000000000000000000000000000 : Int)
    geometryRow006_physicalVolume_numerator_no_slash geometryRow006_physicalVolume_numerator_parse
    geometryRow006_physicalVolume_denominator_parse geometryRow006_physicalVolume_denominator_nonzero

theorem geometryRow006_physicalVolume_read :
    rationalField geometryRowsJson006 "physical_volume" = .ok geometryRowsTyped006.physicalVolume :=
  original_rationalField_of_string geometryRowsJson006 "physical_volume" geometryRow006_physicalVolumeText
    geometryRowsTyped006.physicalVolume geometryRow006_physicalVolume_field geometryRow006_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_physicalVolume_complete"
  err.flush

noncomputable def geometryRow006_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow006_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_meanGapText : String := String.ofList (geometryRow006_meanGapNumeratorChars ++ '/' :: geometryRow006_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_meanGap_before_field"
  err.flush

theorem geometryRow006_meanGap_field :
    geometryRowsJson006.getObjVal? "mean_gap" = .ok (.str geometryRow006_meanGapText) := by rfl

theorem geometryRow006_meanGap_numerator_no_slash :
    geometryRow006_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_meanGap_numerator_parse :
    SourceJson.intChars geometryRow006_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow006_meanGap_denominator_parse :
    SourceJson.intChars geometryRow006_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow006_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_meanGap_parse :
    parseRational geometryRow006_meanGapText = .ok geometryRowsTyped006.meanGap :=
  original_rational_fraction_of_chars geometryRow006_meanGapNumeratorChars geometryRow006_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow006_meanGap_numerator_no_slash geometryRow006_meanGap_numerator_parse
    geometryRow006_meanGap_denominator_parse geometryRow006_meanGap_denominator_nonzero

theorem geometryRow006_meanGap_read :
    rationalField geometryRowsJson006 "mean_gap" = .ok geometryRowsTyped006.meanGap :=
  original_rationalField_of_string geometryRowsJson006 "mean_gap" geometryRow006_meanGapText
    geometryRowsTyped006.meanGap geometryRow006_meanGap_field geometryRow006_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_meanGap_complete"
  err.flush

noncomputable def geometryRow006_jensenBoundNumeratorChars : List Char := ['3', '3', '2', '9', '7', '4', '2', '4', '5', '5', '2', '8', '6', '0', '4', '0', '4', '3', '0', '5', '3', '5', '8', '6', '0', '9', '8', '1', '1', '9', '3', '2', '7', '0', '9', '7', '8', '4', '3', '7', '0', '3', '4', '6', '3', '1', '1', '5', '3', '9', '1', '7', '5', '4', '4', '9', '9', '9', '4', '4', '7', '3', '2', '0', '9', '9', '1', '9', '5', '4', '1', '4', '5', '6', '0', '6', '0', '0', '7', '9', '4', '0', '0', '5', '3', '6', '4', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_jensenBoundDenominatorChars : List Char := ['1', '3', '7', '9', '3', '2', '1', '1', '3', '4', '0', '2', '1', '0', '8', '0', '0', '2', '2', '6', '1', '5', '3', '5', '3', '1', '5', '7', '5', '8', '7', '7', '5', '7', '6', '6', '3', '5', '0', '8', '7', '1', '9', '7', '4', '6', '8', '2', '9', '3', '0', '4', '2', '6', '3', '1', '3', '8', '4', '1', '5', '3', '5', '6', '8', '2', '7', '4', '4', '6', '1', '6', '0', '6', '2', '5', '0', '3', '0', '9', '0', '6', '1', '8', '9', '8', '9', '1', '9', '8', '8', '1', '4', '4', '8', '3', '0', '5', '7', '5', '1', '5', '8', '1', '9', '6', '0', '4', '9', '0', '6', '2', '2', '0', '4', '5', '0', '4', '8', '0', '6', '2', '2', '2', '7', '6', '2', '6', '0', '7']
noncomputable def geometryRow006_jensenBoundText : String := String.ofList (geometryRow006_jensenBoundNumeratorChars ++ '/' :: geometryRow006_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_jensenBound_before_field"
  err.flush

theorem geometryRow006_jensenBound_field :
    geometryRowsJson006.getObjVal? "jensen_bound" = .ok (.str geometryRow006_jensenBoundText) := by rfl

theorem geometryRow006_jensenBound_numerator_no_slash :
    geometryRow006_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow006_jensenBoundNumeratorChars = some (33297424552860404305358609811932709784370346311539175449994473209919541456060079400536406400000000000000000000000 : Int) := by decide +kernel

theorem geometryRow006_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow006_jensenBoundDenominatorChars = some (1379321134021080022615353157587757663508719746829304263138415356827446160625030906189891988144830575158196049062204504806222762607 : Int) := by decide +kernel

theorem geometryRow006_jensenBound_denominator_nonzero : (1379321134021080022615353157587757663508719746829304263138415356827446160625030906189891988144830575158196049062204504806222762607 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_jensenBound_parse :
    parseRational geometryRow006_jensenBoundText = .ok geometryRowsTyped006.jensenBound :=
  original_rational_fraction_of_chars geometryRow006_jensenBoundNumeratorChars geometryRow006_jensenBoundDenominatorChars
    (33297424552860404305358609811932709784370346311539175449994473209919541456060079400536406400000000000000000000000 : Int) (1379321134021080022615353157587757663508719746829304263138415356827446160625030906189891988144830575158196049062204504806222762607 : Int)
    geometryRow006_jensenBound_numerator_no_slash geometryRow006_jensenBound_numerator_parse
    geometryRow006_jensenBound_denominator_parse geometryRow006_jensenBound_denominator_nonzero

theorem geometryRow006_jensenBound_read :
    rationalField geometryRowsJson006 "jensen_bound" = .ok geometryRowsTyped006.jensenBound :=
  original_rationalField_of_string geometryRowsJson006 "jensen_bound" geometryRow006_jensenBoundText
    geometryRowsTyped006.jensenBound geometryRow006_jensenBound_field geometryRow006_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_factorMaxima_before"
  err.flush

theorem geometryRow006_factorMaxima_read :
    rationalArrayField geometryRowsJson006 "factor_maxima" = .ok geometryRowsTyped006.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_gapWeightedMeans_before"
  err.flush

theorem geometryRow006_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson006 "gap_weighted_means" = .ok geometryRowsTyped006.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow006_floorChars : List Char := ['1', '9', '1', '2', '6', '0', '3', '0', '1', '8', '0', '4', '3']
noncomputable def geometryRow006_floorText : String := String.ofList geometryRow006_floorChars

theorem geometryRow006_floor_text_read :
    geometryRowsJson006.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow006_floorText := by rfl

theorem geometryRow006_floor_chars_parse :
    SourceJson.intChars geometryRow006_floorChars = some (1912603018043 : Int) := by decide +kernel

theorem geometryRow006_floor_parse :
    parseInteger geometryRow006_floorText = .ok geometryRowsTyped006.jensenFloorQ96 := by
  simp only [geometryRow006_floorText, parseInteger, String.toList_ofList, geometryRow006_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_006 :
    decodeGeometryRow geometryRowsJson006 = .ok geometryRowsTyped006 :=
  original_geometryRow_of_fields geometryRowsJson006 geometryRowsTyped006 geometryRow006_floorText
    geometryRow006_simplexId_read geometryRow006_vertexIds_read
    geometryRow006_physicalVolume_read geometryRow006_meanGap_read
    geometryRow006_factorMaxima_read geometryRow006_gapWeightedMeans_read
    geometryRow006_jensenBound_read geometryRow006_floor_text_read geometryRow006_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_006_original_decoder_complete"
  err.flush

theorem geometryRow006_shape :
    geometryRowsTyped006.simplexId = 6 ∧
    geometryRowsTyped006.vertexIds.size = 9 ∧ geometryRowsTyped006.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped006.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped006.factorMaxima.size = 10 ∧ geometryRowsTyped006.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson007 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped007 : GeometryRow :=
  { simplexId := 7,
    vertexIds := #[27, 25, 11, 9, 7, 5, 3, 1, 0],
    physicalVolume := ((5210771073194584798264537759023146027 : ℚ) / (221217681678336000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((2409395918681 : ℚ) / (26132400000000 : ℚ)), ((2422000997111 : ℚ) / (26132400000000 : ℚ)), ((1237322948221 : ℚ) / (10452960000000 : ℚ)), ((4538571617971 : ℚ) / (52264800000000 : ℚ)), ((4361313050359 : ℚ) / (52264800000000 : ℚ)), ((791355520547 : ℚ) / (10452960000000 : ℚ)), ((1057744138313 : ℚ) / (26132400000000 : ℚ)), ((890882672317 : ℚ) / (26132400000000 : ℚ)), ((873102867337 : ℚ) / (26132400000000 : ℚ)), ((849283983227 : ℚ) / (26132400000000 : ℚ))],
    jensenBound := ((218180613547586886056816435793150664780516760248912537656730295739242027250044928000000000000000000000000 : ℚ) / (7184564503921793411000997192440298996114572107629361507902928651922642152966838350056576042318514434139947802412932085257 : ℚ)),
    jensenFloorQ96 := (2405998178201 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_simplexId_before"
  err.flush

theorem geometryRow007_simplexId_read :
    geometryRowsJson007.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped007.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_vertexIds_before"
  err.flush

theorem geometryRow007_vertexIds_read :
    geometryRowsJson007.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped007.vertexIds := by decide +kernel

noncomputable def geometryRow007_physicalVolumeNumeratorChars : List Char := ['5', '2', '1', '0', '7', '7', '1', '0', '7', '3', '1', '9', '4', '5', '8', '4', '7', '9', '8', '2', '6', '4', '5', '3', '7', '7', '5', '9', '0', '2', '3', '1', '4', '6', '0', '2', '7']
noncomputable def geometryRow007_physicalVolumeDenominatorChars : List Char := ['2', '2', '1', '2', '1', '7', '6', '8', '1', '6', '7', '8', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_physicalVolumeText : String := String.ofList (geometryRow007_physicalVolumeNumeratorChars ++ '/' :: geometryRow007_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_physicalVolume_before_field"
  err.flush

theorem geometryRow007_physicalVolume_field :
    geometryRowsJson007.getObjVal? "physical_volume" = .ok (.str geometryRow007_physicalVolumeText) := by rfl

theorem geometryRow007_physicalVolume_numerator_no_slash :
    geometryRow007_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow007_physicalVolumeNumeratorChars = some (5210771073194584798264537759023146027 : Int) := by decide +kernel

theorem geometryRow007_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow007_physicalVolumeDenominatorChars = some (221217681678336000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow007_physicalVolume_denominator_nonzero : (221217681678336000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_physicalVolume_parse :
    parseRational geometryRow007_physicalVolumeText = .ok geometryRowsTyped007.physicalVolume :=
  original_rational_fraction_of_chars geometryRow007_physicalVolumeNumeratorChars geometryRow007_physicalVolumeDenominatorChars
    (5210771073194584798264537759023146027 : Int) (221217681678336000000000000000000000000000000000000000000000000 : Int)
    geometryRow007_physicalVolume_numerator_no_slash geometryRow007_physicalVolume_numerator_parse
    geometryRow007_physicalVolume_denominator_parse geometryRow007_physicalVolume_denominator_nonzero

theorem geometryRow007_physicalVolume_read :
    rationalField geometryRowsJson007 "physical_volume" = .ok geometryRowsTyped007.physicalVolume :=
  original_rationalField_of_string geometryRowsJson007 "physical_volume" geometryRow007_physicalVolumeText
    geometryRowsTyped007.physicalVolume geometryRow007_physicalVolume_field geometryRow007_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_physicalVolume_complete"
  err.flush

noncomputable def geometryRow007_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow007_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_meanGapText : String := String.ofList (geometryRow007_meanGapNumeratorChars ++ '/' :: geometryRow007_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_meanGap_before_field"
  err.flush

theorem geometryRow007_meanGap_field :
    geometryRowsJson007.getObjVal? "mean_gap" = .ok (.str geometryRow007_meanGapText) := by rfl

theorem geometryRow007_meanGap_numerator_no_slash :
    geometryRow007_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_meanGap_numerator_parse :
    SourceJson.intChars geometryRow007_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow007_meanGap_denominator_parse :
    SourceJson.intChars geometryRow007_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow007_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_meanGap_parse :
    parseRational geometryRow007_meanGapText = .ok geometryRowsTyped007.meanGap :=
  original_rational_fraction_of_chars geometryRow007_meanGapNumeratorChars geometryRow007_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow007_meanGap_numerator_no_slash geometryRow007_meanGap_numerator_parse
    geometryRow007_meanGap_denominator_parse geometryRow007_meanGap_denominator_nonzero

theorem geometryRow007_meanGap_read :
    rationalField geometryRowsJson007 "mean_gap" = .ok geometryRowsTyped007.meanGap :=
  original_rationalField_of_string geometryRowsJson007 "mean_gap" geometryRow007_meanGapText
    geometryRowsTyped007.meanGap geometryRow007_meanGap_field geometryRow007_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_meanGap_complete"
  err.flush

noncomputable def geometryRow007_jensenBoundNumeratorChars : List Char := ['2', '1', '8', '1', '8', '0', '6', '1', '3', '5', '4', '7', '5', '8', '6', '8', '8', '6', '0', '5', '6', '8', '1', '6', '4', '3', '5', '7', '9', '3', '1', '5', '0', '6', '6', '4', '7', '8', '0', '5', '1', '6', '7', '6', '0', '2', '4', '8', '9', '1', '2', '5', '3', '7', '6', '5', '6', '7', '3', '0', '2', '9', '5', '7', '3', '9', '2', '4', '2', '0', '2', '7', '2', '5', '0', '0', '4', '4', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_jensenBoundDenominatorChars : List Char := ['7', '1', '8', '4', '5', '6', '4', '5', '0', '3', '9', '2', '1', '7', '9', '3', '4', '1', '1', '0', '0', '0', '9', '9', '7', '1', '9', '2', '4', '4', '0', '2', '9', '8', '9', '9', '6', '1', '1', '4', '5', '7', '2', '1', '0', '7', '6', '2', '9', '3', '6', '1', '5', '0', '7', '9', '0', '2', '9', '2', '8', '6', '5', '1', '9', '2', '2', '6', '4', '2', '1', '5', '2', '9', '6', '6', '8', '3', '8', '3', '5', '0', '0', '5', '6', '5', '7', '6', '0', '4', '2', '3', '1', '8', '5', '1', '4', '4', '3', '4', '1', '3', '9', '9', '4', '7', '8', '0', '2', '4', '1', '2', '9', '3', '2', '0', '8', '5', '2', '5', '7']
noncomputable def geometryRow007_jensenBoundText : String := String.ofList (geometryRow007_jensenBoundNumeratorChars ++ '/' :: geometryRow007_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_jensenBound_before_field"
  err.flush

theorem geometryRow007_jensenBound_field :
    geometryRowsJson007.getObjVal? "jensen_bound" = .ok (.str geometryRow007_jensenBoundText) := by rfl

theorem geometryRow007_jensenBound_numerator_no_slash :
    geometryRow007_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow007_jensenBoundNumeratorChars = some (218180613547586886056816435793150664780516760248912537656730295739242027250044928000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow007_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow007_jensenBoundDenominatorChars = some (7184564503921793411000997192440298996114572107629361507902928651922642152966838350056576042318514434139947802412932085257 : Int) := by decide +kernel

theorem geometryRow007_jensenBound_denominator_nonzero : (7184564503921793411000997192440298996114572107629361507902928651922642152966838350056576042318514434139947802412932085257 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_jensenBound_parse :
    parseRational geometryRow007_jensenBoundText = .ok geometryRowsTyped007.jensenBound :=
  original_rational_fraction_of_chars geometryRow007_jensenBoundNumeratorChars geometryRow007_jensenBoundDenominatorChars
    (218180613547586886056816435793150664780516760248912537656730295739242027250044928000000000000000000000000 : Int) (7184564503921793411000997192440298996114572107629361507902928651922642152966838350056576042318514434139947802412932085257 : Int)
    geometryRow007_jensenBound_numerator_no_slash geometryRow007_jensenBound_numerator_parse
    geometryRow007_jensenBound_denominator_parse geometryRow007_jensenBound_denominator_nonzero

theorem geometryRow007_jensenBound_read :
    rationalField geometryRowsJson007 "jensen_bound" = .ok geometryRowsTyped007.jensenBound :=
  original_rationalField_of_string geometryRowsJson007 "jensen_bound" geometryRow007_jensenBoundText
    geometryRowsTyped007.jensenBound geometryRow007_jensenBound_field geometryRow007_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_factorMaxima_before"
  err.flush

theorem geometryRow007_factorMaxima_read :
    rationalArrayField geometryRowsJson007 "factor_maxima" = .ok geometryRowsTyped007.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_gapWeightedMeans_before"
  err.flush

theorem geometryRow007_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson007 "gap_weighted_means" = .ok geometryRowsTyped007.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow007_floorChars : List Char := ['2', '4', '0', '5', '9', '9', '8', '1', '7', '8', '2', '0', '1']
noncomputable def geometryRow007_floorText : String := String.ofList geometryRow007_floorChars

theorem geometryRow007_floor_text_read :
    geometryRowsJson007.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow007_floorText := by rfl

theorem geometryRow007_floor_chars_parse :
    SourceJson.intChars geometryRow007_floorChars = some (2405998178201 : Int) := by decide +kernel

theorem geometryRow007_floor_parse :
    parseInteger geometryRow007_floorText = .ok geometryRowsTyped007.jensenFloorQ96 := by
  simp only [geometryRow007_floorText, parseInteger, String.toList_ofList, geometryRow007_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_007 :
    decodeGeometryRow geometryRowsJson007 = .ok geometryRowsTyped007 :=
  original_geometryRow_of_fields geometryRowsJson007 geometryRowsTyped007 geometryRow007_floorText
    geometryRow007_simplexId_read geometryRow007_vertexIds_read
    geometryRow007_physicalVolume_read geometryRow007_meanGap_read
    geometryRow007_factorMaxima_read geometryRow007_gapWeightedMeans_read
    geometryRow007_jensenBound_read geometryRow007_floor_text_read geometryRow007_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_007_original_decoder_complete"
  err.flush

theorem geometryRow007_shape :
    geometryRowsTyped007.simplexId = 7 ∧
    geometryRowsTyped007.vertexIds.size = 9 ∧ geometryRowsTyped007.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped007.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped007.factorMaxima.size = 10 ∧ geometryRowsTyped007.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock000 : List SourceJson := [geometryRowsJson000, geometryRowsJson001, geometryRowsJson002, geometryRowsJson003, geometryRowsJson004, geometryRowsJson005, geometryRowsJson006, geometryRowsJson007]
noncomputable def geometryRowsTypedBlock000 : List GeometryRow := [geometryRowsTyped000, geometryRowsTyped001, geometryRowsTyped002, geometryRowsTyped003, geometryRowsTyped004, geometryRowsTyped005, geometryRowsTyped006, geometryRowsTyped007]

theorem geometry_Rows_block_000_push_eq (acc : List SourceJson) :
    SimplicesBlock000.blockPush acc = [geometryRowsJson007, geometryRowsJson006, geometryRowsJson005, geometryRowsJson004, geometryRowsJson003, geometryRowsJson002, geometryRowsJson001, geometryRowsJson000] ++ acc := by rfl

theorem geometry_Rows_block_000_reverse (acc : List SourceJson) :
    (SimplicesBlock000.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock000 := by
  rw [geometry_Rows_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_000 :
    geometryRowsJsonBlock000.mapM decodeGeometryRow = .ok geometryRowsTypedBlock000 := by
  simp only [geometryRowsJsonBlock000, geometryRowsTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_000, decode_geometry_Rows_001, decode_geometry_Rows_002, decode_geometry_Rows_003, decode_geometry_Rows_004, decode_geometry_Rows_005, decode_geometry_Rows_006, decode_geometry_Rows_007]
  rfl

theorem geometry_Rows_block_000_length : geometryRowsTypedBlock000.length = 8 := by rfl

#print axioms geometryRow000_simplexId_read
#print axioms geometryRow000_vertexIds_read
#print axioms geometryRow000_physicalVolume_field
#print axioms geometryRow000_physicalVolume_numerator_no_slash
#print axioms geometryRow000_physicalVolume_numerator_parse
#print axioms geometryRow000_physicalVolume_denominator_parse
#print axioms geometryRow000_physicalVolume_denominator_nonzero
#print axioms geometryRow000_physicalVolume_parse
#print axioms geometryRow000_physicalVolume_read
#print axioms geometryRow000_meanGap_field
#print axioms geometryRow000_meanGap_numerator_no_slash
#print axioms geometryRow000_meanGap_numerator_parse
#print axioms geometryRow000_meanGap_denominator_parse
#print axioms geometryRow000_meanGap_denominator_nonzero
#print axioms geometryRow000_meanGap_parse
#print axioms geometryRow000_meanGap_read
#print axioms geometryRow000_jensenBound_field
#print axioms geometryRow000_jensenBound_numerator_no_slash
#print axioms geometryRow000_jensenBound_numerator_parse
#print axioms geometryRow000_jensenBound_denominator_parse
#print axioms geometryRow000_jensenBound_denominator_nonzero
#print axioms geometryRow000_jensenBound_parse
#print axioms geometryRow000_jensenBound_read
#print axioms geometryRow000_factorMaxima_read
#print axioms geometryRow000_gapWeightedMeans_read
#print axioms geometryRow000_floor_text_read
#print axioms geometryRow000_floor_chars_parse
#print axioms geometryRow000_floor_parse
#print axioms decode_geometry_Rows_000
#print axioms geometryRow000_shape
#print axioms geometryRow001_simplexId_read
#print axioms geometryRow001_vertexIds_read
#print axioms geometryRow001_physicalVolume_field
#print axioms geometryRow001_physicalVolume_numerator_no_slash
#print axioms geometryRow001_physicalVolume_numerator_parse
#print axioms geometryRow001_physicalVolume_denominator_parse
#print axioms geometryRow001_physicalVolume_denominator_nonzero
#print axioms geometryRow001_physicalVolume_parse
#print axioms geometryRow001_physicalVolume_read
#print axioms geometryRow001_meanGap_field
#print axioms geometryRow001_meanGap_numerator_no_slash
#print axioms geometryRow001_meanGap_numerator_parse
#print axioms geometryRow001_meanGap_denominator_parse
#print axioms geometryRow001_meanGap_denominator_nonzero
#print axioms geometryRow001_meanGap_parse
#print axioms geometryRow001_meanGap_read
#print axioms geometryRow001_jensenBound_field
#print axioms geometryRow001_jensenBound_numerator_no_slash
#print axioms geometryRow001_jensenBound_numerator_parse
#print axioms geometryRow001_jensenBound_denominator_parse
#print axioms geometryRow001_jensenBound_denominator_nonzero
#print axioms geometryRow001_jensenBound_parse
#print axioms geometryRow001_jensenBound_read
#print axioms geometryRow001_factorMaxima_read
#print axioms geometryRow001_gapWeightedMeans_read
#print axioms geometryRow001_floor_text_read
#print axioms geometryRow001_floor_chars_parse
#print axioms geometryRow001_floor_parse
#print axioms decode_geometry_Rows_001
#print axioms geometryRow001_shape
#print axioms geometryRow002_simplexId_read
#print axioms geometryRow002_vertexIds_read
#print axioms geometryRow002_physicalVolume_field
#print axioms geometryRow002_physicalVolume_numerator_no_slash
#print axioms geometryRow002_physicalVolume_numerator_parse
#print axioms geometryRow002_physicalVolume_denominator_parse
#print axioms geometryRow002_physicalVolume_denominator_nonzero
#print axioms geometryRow002_physicalVolume_parse
#print axioms geometryRow002_physicalVolume_read
#print axioms geometryRow002_meanGap_field
#print axioms geometryRow002_meanGap_numerator_no_slash
#print axioms geometryRow002_meanGap_numerator_parse
#print axioms geometryRow002_meanGap_denominator_parse
#print axioms geometryRow002_meanGap_denominator_nonzero
#print axioms geometryRow002_meanGap_parse
#print axioms geometryRow002_meanGap_read
#print axioms geometryRow002_jensenBound_field
#print axioms geometryRow002_jensenBound_numerator_no_slash
#print axioms geometryRow002_jensenBound_numerator_parse
#print axioms geometryRow002_jensenBound_denominator_parse
#print axioms geometryRow002_jensenBound_denominator_nonzero
#print axioms geometryRow002_jensenBound_parse
#print axioms geometryRow002_jensenBound_read
#print axioms geometryRow002_factorMaxima_read
#print axioms geometryRow002_gapWeightedMeans_read
#print axioms geometryRow002_floor_text_read
#print axioms geometryRow002_floor_chars_parse
#print axioms geometryRow002_floor_parse
#print axioms decode_geometry_Rows_002
#print axioms geometryRow002_shape
#print axioms geometryRow003_simplexId_read
#print axioms geometryRow003_vertexIds_read
#print axioms geometryRow003_physicalVolume_field
#print axioms geometryRow003_physicalVolume_numerator_no_slash
#print axioms geometryRow003_physicalVolume_numerator_parse
#print axioms geometryRow003_physicalVolume_denominator_parse
#print axioms geometryRow003_physicalVolume_denominator_nonzero
#print axioms geometryRow003_physicalVolume_parse
#print axioms geometryRow003_physicalVolume_read
#print axioms geometryRow003_meanGap_field
#print axioms geometryRow003_meanGap_numerator_no_slash
#print axioms geometryRow003_meanGap_numerator_parse
#print axioms geometryRow003_meanGap_denominator_parse
#print axioms geometryRow003_meanGap_denominator_nonzero
#print axioms geometryRow003_meanGap_parse
#print axioms geometryRow003_meanGap_read
#print axioms geometryRow003_jensenBound_field
#print axioms geometryRow003_jensenBound_numerator_no_slash
#print axioms geometryRow003_jensenBound_numerator_parse
#print axioms geometryRow003_jensenBound_denominator_parse
#print axioms geometryRow003_jensenBound_denominator_nonzero
#print axioms geometryRow003_jensenBound_parse
#print axioms geometryRow003_jensenBound_read
#print axioms geometryRow003_factorMaxima_read
#print axioms geometryRow003_gapWeightedMeans_read
#print axioms geometryRow003_floor_text_read
#print axioms geometryRow003_floor_chars_parse
#print axioms geometryRow003_floor_parse
#print axioms decode_geometry_Rows_003
#print axioms geometryRow003_shape
#print axioms geometryRow004_simplexId_read
#print axioms geometryRow004_vertexIds_read
#print axioms geometryRow004_physicalVolume_field
#print axioms geometryRow004_physicalVolume_numerator_no_slash
#print axioms geometryRow004_physicalVolume_numerator_parse
#print axioms geometryRow004_physicalVolume_denominator_parse
#print axioms geometryRow004_physicalVolume_denominator_nonzero
#print axioms geometryRow004_physicalVolume_parse
#print axioms geometryRow004_physicalVolume_read
#print axioms geometryRow004_meanGap_field
#print axioms geometryRow004_meanGap_numerator_no_slash
#print axioms geometryRow004_meanGap_numerator_parse
#print axioms geometryRow004_meanGap_denominator_parse
#print axioms geometryRow004_meanGap_denominator_nonzero
#print axioms geometryRow004_meanGap_parse
#print axioms geometryRow004_meanGap_read
#print axioms geometryRow004_jensenBound_field
#print axioms geometryRow004_jensenBound_numerator_no_slash
#print axioms geometryRow004_jensenBound_numerator_parse
#print axioms geometryRow004_jensenBound_denominator_parse
#print axioms geometryRow004_jensenBound_denominator_nonzero
#print axioms geometryRow004_jensenBound_parse
#print axioms geometryRow004_jensenBound_read
#print axioms geometryRow004_factorMaxima_read
#print axioms geometryRow004_gapWeightedMeans_read
#print axioms geometryRow004_floor_text_read
#print axioms geometryRow004_floor_chars_parse
#print axioms geometryRow004_floor_parse
#print axioms decode_geometry_Rows_004
#print axioms geometryRow004_shape
#print axioms geometryRow005_simplexId_read
#print axioms geometryRow005_vertexIds_read
#print axioms geometryRow005_physicalVolume_field
#print axioms geometryRow005_physicalVolume_numerator_no_slash
#print axioms geometryRow005_physicalVolume_numerator_parse
#print axioms geometryRow005_physicalVolume_denominator_parse
#print axioms geometryRow005_physicalVolume_denominator_nonzero
#print axioms geometryRow005_physicalVolume_parse
#print axioms geometryRow005_physicalVolume_read
#print axioms geometryRow005_meanGap_field
#print axioms geometryRow005_meanGap_numerator_no_slash
#print axioms geometryRow005_meanGap_numerator_parse
#print axioms geometryRow005_meanGap_denominator_parse
#print axioms geometryRow005_meanGap_denominator_nonzero
#print axioms geometryRow005_meanGap_parse
#print axioms geometryRow005_meanGap_read
#print axioms geometryRow005_jensenBound_field
#print axioms geometryRow005_jensenBound_numerator_no_slash
#print axioms geometryRow005_jensenBound_numerator_parse
#print axioms geometryRow005_jensenBound_denominator_parse
#print axioms geometryRow005_jensenBound_denominator_nonzero
#print axioms geometryRow005_jensenBound_parse
#print axioms geometryRow005_jensenBound_read
#print axioms geometryRow005_factorMaxima_read
#print axioms geometryRow005_gapWeightedMeans_read
#print axioms geometryRow005_floor_text_read
#print axioms geometryRow005_floor_chars_parse
#print axioms geometryRow005_floor_parse
#print axioms decode_geometry_Rows_005
#print axioms geometryRow005_shape
#print axioms geometryRow006_simplexId_read
#print axioms geometryRow006_vertexIds_read
#print axioms geometryRow006_physicalVolume_field
#print axioms geometryRow006_physicalVolume_numerator_no_slash
#print axioms geometryRow006_physicalVolume_numerator_parse
#print axioms geometryRow006_physicalVolume_denominator_parse
#print axioms geometryRow006_physicalVolume_denominator_nonzero
#print axioms geometryRow006_physicalVolume_parse
#print axioms geometryRow006_physicalVolume_read
#print axioms geometryRow006_meanGap_field
#print axioms geometryRow006_meanGap_numerator_no_slash
#print axioms geometryRow006_meanGap_numerator_parse
#print axioms geometryRow006_meanGap_denominator_parse
#print axioms geometryRow006_meanGap_denominator_nonzero
#print axioms geometryRow006_meanGap_parse
#print axioms geometryRow006_meanGap_read
#print axioms geometryRow006_jensenBound_field
#print axioms geometryRow006_jensenBound_numerator_no_slash
#print axioms geometryRow006_jensenBound_numerator_parse
#print axioms geometryRow006_jensenBound_denominator_parse
#print axioms geometryRow006_jensenBound_denominator_nonzero
#print axioms geometryRow006_jensenBound_parse
#print axioms geometryRow006_jensenBound_read
#print axioms geometryRow006_factorMaxima_read
#print axioms geometryRow006_gapWeightedMeans_read
#print axioms geometryRow006_floor_text_read
#print axioms geometryRow006_floor_chars_parse
#print axioms geometryRow006_floor_parse
#print axioms decode_geometry_Rows_006
#print axioms geometryRow006_shape
#print axioms geometryRow007_simplexId_read
#print axioms geometryRow007_vertexIds_read
#print axioms geometryRow007_physicalVolume_field
#print axioms geometryRow007_physicalVolume_numerator_no_slash
#print axioms geometryRow007_physicalVolume_numerator_parse
#print axioms geometryRow007_physicalVolume_denominator_parse
#print axioms geometryRow007_physicalVolume_denominator_nonzero
#print axioms geometryRow007_physicalVolume_parse
#print axioms geometryRow007_physicalVolume_read
#print axioms geometryRow007_meanGap_field
#print axioms geometryRow007_meanGap_numerator_no_slash
#print axioms geometryRow007_meanGap_numerator_parse
#print axioms geometryRow007_meanGap_denominator_parse
#print axioms geometryRow007_meanGap_denominator_nonzero
#print axioms geometryRow007_meanGap_parse
#print axioms geometryRow007_meanGap_read
#print axioms geometryRow007_jensenBound_field
#print axioms geometryRow007_jensenBound_numerator_no_slash
#print axioms geometryRow007_jensenBound_numerator_parse
#print axioms geometryRow007_jensenBound_denominator_parse
#print axioms geometryRow007_jensenBound_denominator_nonzero
#print axioms geometryRow007_jensenBound_parse
#print axioms geometryRow007_jensenBound_read
#print axioms geometryRow007_factorMaxima_read
#print axioms geometryRow007_gapWeightedMeans_read
#print axioms geometryRow007_floor_text_read
#print axioms geometryRow007_floor_chars_parse
#print axioms geometryRow007_floor_parse
#print axioms decode_geometry_Rows_007
#print axioms geometryRow007_shape
#print axioms geometry_Rows_block_000_push_eq
#print axioms geometry_Rows_block_000_reverse
#print axioms decode_geometry_Rows_block_000
#print axioms geometry_Rows_block_000_length

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
