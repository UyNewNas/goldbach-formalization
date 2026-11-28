import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock007

/-! Local typed certificates for original cell 06, rows 56 through 63.
This owner imports only its own original parser leaf.  No cumulative typed
prefix, whole-array parser value, or completed geometric archive is imported.
The original rational decoder and GeometryRow record fields are unchanged. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson056 : SourceJson :=
  (SimplicesBlock007.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped056 : GeometryRow :=
  { simplexId := 56,
    vertexIds := #[32, 30, 28, 27, 23, 13, 10, 1, 0],
    physicalVolume := ((1085200221715174936027765719327094037 : ℚ) / (163333000832400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((277454140061828222447 : ℚ) / (3199182368243400000000 : ℚ)), ((40548043981131554723 : ℚ) / (457026052606200000000 : ℚ)), ((1657576707292022207 : ℚ) / (13909488557580000000 : ℚ)), ((99059936396744249557 : ℚ) / (1066394122747800000000 : ℚ)), ((32826814125151936279 : ℚ) / (355464707582600000000 : ℚ)), ((5209024418018950993 : ℚ) / (72708690187350000000 : ℚ)), ((10706205900355779581 : ℚ) / (290834760749400000000 : ℚ)), ((9610596611909945711 : ℚ) / (290834760749400000000 : ℚ)), ((9452514009954089231 : ℚ) / (290834760749400000000 : ℚ)), ((13833366780550595281 : ℚ) / (457026052606200000000 : ℚ))],
    jensenBound := ((7983519949226149533277843278737912305185383488207258105582033813448622335352688858963029363406111634691514637320427185599442482359937801973523968700816640000000000000000000000 : ℚ) / (137093667932836473000560333395857934411669415407715389808683891037771788821977330047961978154062701290303533259463255618391790923597159460994132705796954065300751475217429309678496083288952203 : ℚ)),
    jensenFloorQ96 := (4613777029315 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_simplexId_before"
  err.flush

theorem geometryRow056_simplexId_read :
    geometryRowsJson056.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped056.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_vertexIds_before"
  err.flush

theorem geometryRow056_vertexIds_read :
    geometryRowsJson056.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped056.vertexIds := by decide +kernel

noncomputable def geometryRow056_physicalVolumeNumeratorChars : List Char := ['1', '0', '8', '5', '2', '0', '0', '2', '2', '1', '7', '1', '5', '1', '7', '4', '9', '3', '6', '0', '2', '7', '7', '6', '5', '7', '1', '9', '3', '2', '7', '0', '9', '4', '0', '3', '7']
noncomputable def geometryRow056_physicalVolumeDenominatorChars : List Char := ['1', '6', '3', '3', '3', '3', '0', '0', '0', '8', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow056_physicalVolumeText : String := String.ofList (geometryRow056_physicalVolumeNumeratorChars ++ '/' :: geometryRow056_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_physicalVolume_before_field"
  err.flush

theorem geometryRow056_physicalVolume_field :
    geometryRowsJson056.getObjVal? "physical_volume" = .ok (.str geometryRow056_physicalVolumeText) := by rfl

theorem geometryRow056_physicalVolume_numerator_no_slash :
    geometryRow056_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow056_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow056_physicalVolumeNumeratorChars = some (1085200221715174936027765719327094037 : Int) := by decide +kernel

theorem geometryRow056_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow056_physicalVolumeDenominatorChars = some (163333000832400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow056_physicalVolume_denominator_nonzero : (163333000832400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow056_physicalVolume_parse :
    parseRational geometryRow056_physicalVolumeText = .ok geometryRowsTyped056.physicalVolume :=
  original_rational_fraction_of_chars geometryRow056_physicalVolumeNumeratorChars geometryRow056_physicalVolumeDenominatorChars
    (1085200221715174936027765719327094037 : Int) (163333000832400000000000000000000000000000000000000000000000000 : Int)
    geometryRow056_physicalVolume_numerator_no_slash geometryRow056_physicalVolume_numerator_parse
    geometryRow056_physicalVolume_denominator_parse geometryRow056_physicalVolume_denominator_nonzero

theorem geometryRow056_physicalVolume_read :
    rationalField geometryRowsJson056 "physical_volume" = .ok geometryRowsTyped056.physicalVolume :=
  original_rationalField_of_string geometryRowsJson056 "physical_volume" geometryRow056_physicalVolumeText
    geometryRowsTyped056.physicalVolume geometryRow056_physicalVolume_field geometryRow056_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_physicalVolume_complete"
  err.flush

noncomputable def geometryRow056_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow056_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow056_meanGapText : String := String.ofList (geometryRow056_meanGapNumeratorChars ++ '/' :: geometryRow056_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_meanGap_before_field"
  err.flush

theorem geometryRow056_meanGap_field :
    geometryRowsJson056.getObjVal? "mean_gap" = .ok (.str geometryRow056_meanGapText) := by rfl

theorem geometryRow056_meanGap_numerator_no_slash :
    geometryRow056_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow056_meanGap_numerator_parse :
    SourceJson.intChars geometryRow056_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow056_meanGap_denominator_parse :
    SourceJson.intChars geometryRow056_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow056_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow056_meanGap_parse :
    parseRational geometryRow056_meanGapText = .ok geometryRowsTyped056.meanGap :=
  original_rational_fraction_of_chars geometryRow056_meanGapNumeratorChars geometryRow056_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow056_meanGap_numerator_no_slash geometryRow056_meanGap_numerator_parse
    geometryRow056_meanGap_denominator_parse geometryRow056_meanGap_denominator_nonzero

theorem geometryRow056_meanGap_read :
    rationalField geometryRowsJson056 "mean_gap" = .ok geometryRowsTyped056.meanGap :=
  original_rationalField_of_string geometryRowsJson056 "mean_gap" geometryRow056_meanGapText
    geometryRowsTyped056.meanGap geometryRow056_meanGap_field geometryRow056_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_meanGap_complete"
  err.flush

noncomputable def geometryRow056_jensenBoundNumeratorChars : List Char := ['7', '9', '8', '3', '5', '1', '9', '9', '4', '9', '2', '2', '6', '1', '4', '9', '5', '3', '3', '2', '7', '7', '8', '4', '3', '2', '7', '8', '7', '3', '7', '9', '1', '2', '3', '0', '5', '1', '8', '5', '3', '8', '3', '4', '8', '8', '2', '0', '7', '2', '5', '8', '1', '0', '5', '5', '8', '2', '0', '3', '3', '8', '1', '3', '4', '4', '8', '6', '2', '2', '3', '3', '5', '3', '5', '2', '6', '8', '8', '8', '5', '8', '9', '6', '3', '0', '2', '9', '3', '6', '3', '4', '0', '6', '1', '1', '1', '6', '3', '4', '6', '9', '1', '5', '1', '4', '6', '3', '7', '3', '2', '0', '4', '2', '7', '1', '8', '5', '5', '9', '9', '4', '4', '2', '4', '8', '2', '3', '5', '9', '9', '3', '7', '8', '0', '1', '9', '7', '3', '5', '2', '3', '9', '6', '8', '7', '0', '0', '8', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow056_jensenBoundDenominatorChars : List Char := ['1', '3', '7', '0', '9', '3', '6', '6', '7', '9', '3', '2', '8', '3', '6', '4', '7', '3', '0', '0', '0', '5', '6', '0', '3', '3', '3', '3', '9', '5', '8', '5', '7', '9', '3', '4', '4', '1', '1', '6', '6', '9', '4', '1', '5', '4', '0', '7', '7', '1', '5', '3', '8', '9', '8', '0', '8', '6', '8', '3', '8', '9', '1', '0', '3', '7', '7', '7', '1', '7', '8', '8', '8', '2', '1', '9', '7', '7', '3', '3', '0', '0', '4', '7', '9', '6', '1', '9', '7', '8', '1', '5', '4', '0', '6', '2', '7', '0', '1', '2', '9', '0', '3', '0', '3', '5', '3', '3', '2', '5', '9', '4', '6', '3', '2', '5', '5', '6', '1', '8', '3', '9', '1', '7', '9', '0', '9', '2', '3', '5', '9', '7', '1', '5', '9', '4', '6', '0', '9', '9', '4', '1', '3', '2', '7', '0', '5', '7', '9', '6', '9', '5', '4', '0', '6', '5', '3', '0', '0', '7', '5', '1', '4', '7', '5', '2', '1', '7', '4', '2', '9', '3', '0', '9', '6', '7', '8', '4', '9', '6', '0', '8', '3', '2', '8', '8', '9', '5', '2', '2', '0', '3']
noncomputable def geometryRow056_jensenBoundText : String := String.ofList (geometryRow056_jensenBoundNumeratorChars ++ '/' :: geometryRow056_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_jensenBound_before_field"
  err.flush

theorem geometryRow056_jensenBound_field :
    geometryRowsJson056.getObjVal? "jensen_bound" = .ok (.str geometryRow056_jensenBoundText) := by rfl

theorem geometryRow056_jensenBound_numerator_no_slash :
    geometryRow056_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow056_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow056_jensenBoundNumeratorChars = some (7983519949226149533277843278737912305185383488207258105582033813448622335352688858963029363406111634691514637320427185599442482359937801973523968700816640000000000000000000000 : Int) := by decide +kernel

theorem geometryRow056_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow056_jensenBoundDenominatorChars = some (137093667932836473000560333395857934411669415407715389808683891037771788821977330047961978154062701290303533259463255618391790923597159460994132705796954065300751475217429309678496083288952203 : Int) := by decide +kernel

theorem geometryRow056_jensenBound_denominator_nonzero : (137093667932836473000560333395857934411669415407715389808683891037771788821977330047961978154062701290303533259463255618391790923597159460994132705796954065300751475217429309678496083288952203 : Int) ≠ 0 := by decide +kernel

theorem geometryRow056_jensenBound_parse :
    parseRational geometryRow056_jensenBoundText = .ok geometryRowsTyped056.jensenBound :=
  original_rational_fraction_of_chars geometryRow056_jensenBoundNumeratorChars geometryRow056_jensenBoundDenominatorChars
    (7983519949226149533277843278737912305185383488207258105582033813448622335352688858963029363406111634691514637320427185599442482359937801973523968700816640000000000000000000000 : Int) (137093667932836473000560333395857934411669415407715389808683891037771788821977330047961978154062701290303533259463255618391790923597159460994132705796954065300751475217429309678496083288952203 : Int)
    geometryRow056_jensenBound_numerator_no_slash geometryRow056_jensenBound_numerator_parse
    geometryRow056_jensenBound_denominator_parse geometryRow056_jensenBound_denominator_nonzero

theorem geometryRow056_jensenBound_read :
    rationalField geometryRowsJson056 "jensen_bound" = .ok geometryRowsTyped056.jensenBound :=
  original_rationalField_of_string geometryRowsJson056 "jensen_bound" geometryRow056_jensenBoundText
    geometryRowsTyped056.jensenBound geometryRow056_jensenBound_field geometryRow056_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_factorMaxima_before"
  err.flush

theorem geometryRow056_factorMaxima_read :
    rationalArrayField geometryRowsJson056 "factor_maxima" = .ok geometryRowsTyped056.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_gapWeightedMeans_before"
  err.flush

theorem geometryRow056_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson056 "gap_weighted_means" = .ok geometryRowsTyped056.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow056_floorChars : List Char := ['4', '6', '1', '3', '7', '7', '7', '0', '2', '9', '3', '1', '5']
noncomputable def geometryRow056_floorText : String := String.ofList geometryRow056_floorChars

theorem geometryRow056_floor_text_read :
    geometryRowsJson056.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow056_floorText := by rfl

theorem geometryRow056_floor_chars_parse :
    SourceJson.intChars geometryRow056_floorChars = some (4613777029315 : Int) := by decide +kernel

theorem geometryRow056_floor_parse :
    parseInteger geometryRow056_floorText = .ok geometryRowsTyped056.jensenFloorQ96 := by
  simp only [geometryRow056_floorText, parseInteger, String.toList_ofList, geometryRow056_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_056 :
    decodeGeometryRow geometryRowsJson056 = .ok geometryRowsTyped056 :=
  original_geometryRow_of_fields geometryRowsJson056 geometryRowsTyped056 geometryRow056_floorText
    geometryRow056_simplexId_read geometryRow056_vertexIds_read
    geometryRow056_physicalVolume_read geometryRow056_meanGap_read
    geometryRow056_factorMaxima_read geometryRow056_gapWeightedMeans_read
    geometryRow056_jensenBound_read geometryRow056_floor_text_read geometryRow056_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_056_original_decoder_complete"
  err.flush

theorem geometryRow056_shape :
    geometryRowsTyped056.simplexId = 56 ∧
    geometryRowsTyped056.vertexIds.size = 9 ∧ geometryRowsTyped056.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped056.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped056.factorMaxima.size = 10 ∧ geometryRowsTyped056.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson057 : SourceJson :=
  (SimplicesBlock007.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped057 : GeometryRow :=
  { simplexId := 57,
    vertexIds := #[32, 30, 28, 27, 23, 13, 10, 8, 0],
    physicalVolume := ((24014216631271991664211135901011537457 : ℚ) / (359999267140800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((274260358459 : ℚ) / (3187800000000 : ℚ)), ((278470807597 : ℚ) / (3187800000000 : ℚ)), ((9928511851 : ℚ) / (83160000000 : ℚ)), ((55121824601 : ℚ) / (597712500000 : ℚ)), ((27398509483 : ℚ) / (298856250000 : ℚ)), ((63265337167 : ℚ) / (869400000000 : ℚ)), ((4626370943 : ℚ) / (124200000000 : ℚ)), ((14664198943 : ℚ) / (434700000000 : ℚ)), ((14427918703 : ℚ) / (434700000000 : ℚ)), ((285111490877 : ℚ) / (9563400000000 : ℚ))],
    jensenBound := ((16913029298420788832697432576394442677618715640592877161287733288826250000000000000000000 : ℚ) / (59293357798632689762378923973720625997337246110748191601669320898584518212235709541735094497230423645927 : ℚ)),
    jensenFloorQ96 := (22599297520213 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_simplexId_before"
  err.flush

theorem geometryRow057_simplexId_read :
    geometryRowsJson057.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped057.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_vertexIds_before"
  err.flush

theorem geometryRow057_vertexIds_read :
    geometryRowsJson057.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped057.vertexIds := by decide +kernel

noncomputable def geometryRow057_physicalVolumeNumeratorChars : List Char := ['2', '4', '0', '1', '4', '2', '1', '6', '6', '3', '1', '2', '7', '1', '9', '9', '1', '6', '6', '4', '2', '1', '1', '1', '3', '5', '9', '0', '1', '0', '1', '1', '5', '3', '7', '4', '5', '7']
noncomputable def geometryRow057_physicalVolumeDenominatorChars : List Char := ['3', '5', '9', '9', '9', '9', '2', '6', '7', '1', '4', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow057_physicalVolumeText : String := String.ofList (geometryRow057_physicalVolumeNumeratorChars ++ '/' :: geometryRow057_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_physicalVolume_before_field"
  err.flush

theorem geometryRow057_physicalVolume_field :
    geometryRowsJson057.getObjVal? "physical_volume" = .ok (.str geometryRow057_physicalVolumeText) := by rfl

theorem geometryRow057_physicalVolume_numerator_no_slash :
    geometryRow057_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow057_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow057_physicalVolumeNumeratorChars = some (24014216631271991664211135901011537457 : Int) := by decide +kernel

theorem geometryRow057_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow057_physicalVolumeDenominatorChars = some (359999267140800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow057_physicalVolume_denominator_nonzero : (359999267140800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow057_physicalVolume_parse :
    parseRational geometryRow057_physicalVolumeText = .ok geometryRowsTyped057.physicalVolume :=
  original_rational_fraction_of_chars geometryRow057_physicalVolumeNumeratorChars geometryRow057_physicalVolumeDenominatorChars
    (24014216631271991664211135901011537457 : Int) (359999267140800000000000000000000000000000000000000000000000000 : Int)
    geometryRow057_physicalVolume_numerator_no_slash geometryRow057_physicalVolume_numerator_parse
    geometryRow057_physicalVolume_denominator_parse geometryRow057_physicalVolume_denominator_nonzero

theorem geometryRow057_physicalVolume_read :
    rationalField geometryRowsJson057 "physical_volume" = .ok geometryRowsTyped057.physicalVolume :=
  original_rationalField_of_string geometryRowsJson057 "physical_volume" geometryRow057_physicalVolumeText
    geometryRowsTyped057.physicalVolume geometryRow057_physicalVolume_field geometryRow057_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_physicalVolume_complete"
  err.flush

noncomputable def geometryRow057_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow057_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow057_meanGapText : String := String.ofList (geometryRow057_meanGapNumeratorChars ++ '/' :: geometryRow057_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_meanGap_before_field"
  err.flush

theorem geometryRow057_meanGap_field :
    geometryRowsJson057.getObjVal? "mean_gap" = .ok (.str geometryRow057_meanGapText) := by rfl

theorem geometryRow057_meanGap_numerator_no_slash :
    geometryRow057_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow057_meanGap_numerator_parse :
    SourceJson.intChars geometryRow057_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow057_meanGap_denominator_parse :
    SourceJson.intChars geometryRow057_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow057_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow057_meanGap_parse :
    parseRational geometryRow057_meanGapText = .ok geometryRowsTyped057.meanGap :=
  original_rational_fraction_of_chars geometryRow057_meanGapNumeratorChars geometryRow057_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow057_meanGap_numerator_no_slash geometryRow057_meanGap_numerator_parse
    geometryRow057_meanGap_denominator_parse geometryRow057_meanGap_denominator_nonzero

theorem geometryRow057_meanGap_read :
    rationalField geometryRowsJson057 "mean_gap" = .ok geometryRowsTyped057.meanGap :=
  original_rationalField_of_string geometryRowsJson057 "mean_gap" geometryRow057_meanGapText
    geometryRowsTyped057.meanGap geometryRow057_meanGap_field geometryRow057_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_meanGap_complete"
  err.flush

noncomputable def geometryRow057_jensenBoundNumeratorChars : List Char := ['1', '6', '9', '1', '3', '0', '2', '9', '2', '9', '8', '4', '2', '0', '7', '8', '8', '8', '3', '2', '6', '9', '7', '4', '3', '2', '5', '7', '6', '3', '9', '4', '4', '4', '2', '6', '7', '7', '6', '1', '8', '7', '1', '5', '6', '4', '0', '5', '9', '2', '8', '7', '7', '1', '6', '1', '2', '8', '7', '7', '3', '3', '2', '8', '8', '8', '2', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow057_jensenBoundDenominatorChars : List Char := ['5', '9', '2', '9', '3', '3', '5', '7', '7', '9', '8', '6', '3', '2', '6', '8', '9', '7', '6', '2', '3', '7', '8', '9', '2', '3', '9', '7', '3', '7', '2', '0', '6', '2', '5', '9', '9', '7', '3', '3', '7', '2', '4', '6', '1', '1', '0', '7', '4', '8', '1', '9', '1', '6', '0', '1', '6', '6', '9', '3', '2', '0', '8', '9', '8', '5', '8', '4', '5', '1', '8', '2', '1', '2', '2', '3', '5', '7', '0', '9', '5', '4', '1', '7', '3', '5', '0', '9', '4', '4', '9', '7', '2', '3', '0', '4', '2', '3', '6', '4', '5', '9', '2', '7']
noncomputable def geometryRow057_jensenBoundText : String := String.ofList (geometryRow057_jensenBoundNumeratorChars ++ '/' :: geometryRow057_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_jensenBound_before_field"
  err.flush

theorem geometryRow057_jensenBound_field :
    geometryRowsJson057.getObjVal? "jensen_bound" = .ok (.str geometryRow057_jensenBoundText) := by rfl

theorem geometryRow057_jensenBound_numerator_no_slash :
    geometryRow057_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow057_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow057_jensenBoundNumeratorChars = some (16913029298420788832697432576394442677618715640592877161287733288826250000000000000000000 : Int) := by decide +kernel

theorem geometryRow057_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow057_jensenBoundDenominatorChars = some (59293357798632689762378923973720625997337246110748191601669320898584518212235709541735094497230423645927 : Int) := by decide +kernel

theorem geometryRow057_jensenBound_denominator_nonzero : (59293357798632689762378923973720625997337246110748191601669320898584518212235709541735094497230423645927 : Int) ≠ 0 := by decide +kernel

theorem geometryRow057_jensenBound_parse :
    parseRational geometryRow057_jensenBoundText = .ok geometryRowsTyped057.jensenBound :=
  original_rational_fraction_of_chars geometryRow057_jensenBoundNumeratorChars geometryRow057_jensenBoundDenominatorChars
    (16913029298420788832697432576394442677618715640592877161287733288826250000000000000000000 : Int) (59293357798632689762378923973720625997337246110748191601669320898584518212235709541735094497230423645927 : Int)
    geometryRow057_jensenBound_numerator_no_slash geometryRow057_jensenBound_numerator_parse
    geometryRow057_jensenBound_denominator_parse geometryRow057_jensenBound_denominator_nonzero

theorem geometryRow057_jensenBound_read :
    rationalField geometryRowsJson057 "jensen_bound" = .ok geometryRowsTyped057.jensenBound :=
  original_rationalField_of_string geometryRowsJson057 "jensen_bound" geometryRow057_jensenBoundText
    geometryRowsTyped057.jensenBound geometryRow057_jensenBound_field geometryRow057_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_factorMaxima_before"
  err.flush

theorem geometryRow057_factorMaxima_read :
    rationalArrayField geometryRowsJson057 "factor_maxima" = .ok geometryRowsTyped057.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_gapWeightedMeans_before"
  err.flush

theorem geometryRow057_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson057 "gap_weighted_means" = .ok geometryRowsTyped057.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow057_floorChars : List Char := ['2', '2', '5', '9', '9', '2', '9', '7', '5', '2', '0', '2', '1', '3']
noncomputable def geometryRow057_floorText : String := String.ofList geometryRow057_floorChars

theorem geometryRow057_floor_text_read :
    geometryRowsJson057.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow057_floorText := by rfl

theorem geometryRow057_floor_chars_parse :
    SourceJson.intChars geometryRow057_floorChars = some (22599297520213 : Int) := by decide +kernel

theorem geometryRow057_floor_parse :
    parseInteger geometryRow057_floorText = .ok geometryRowsTyped057.jensenFloorQ96 := by
  simp only [geometryRow057_floorText, parseInteger, String.toList_ofList, geometryRow057_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_057 :
    decodeGeometryRow geometryRowsJson057 = .ok geometryRowsTyped057 :=
  original_geometryRow_of_fields geometryRowsJson057 geometryRowsTyped057 geometryRow057_floorText
    geometryRow057_simplexId_read geometryRow057_vertexIds_read
    geometryRow057_physicalVolume_read geometryRow057_meanGap_read
    geometryRow057_factorMaxima_read geometryRow057_gapWeightedMeans_read
    geometryRow057_jensenBound_read geometryRow057_floor_text_read geometryRow057_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_057_original_decoder_complete"
  err.flush

theorem geometryRow057_shape :
    geometryRowsTyped057.simplexId = 57 ∧
    geometryRowsTyped057.vertexIds.size = 9 ∧ geometryRowsTyped057.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped057.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped057.factorMaxima.size = 10 ∧ geometryRowsTyped057.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson058 : SourceJson :=
  (SimplicesBlock007.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped058 : GeometryRow :=
  { simplexId := 58,
    vertexIds := #[32, 30, 28, 27, 23, 22, 13, 4, 0],
    physicalVolume := ((25367863202890730420209355148172277 : ℚ) / (5972210064450000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((96707389 : ℚ) / (66220000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((765619 : ℚ) / (10062500 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((568628673089345769779 : ℚ) / (6628102015065300000000 : ℚ)), ((6763910531024394647 : ℚ) / (77070953663550000000 : ℚ)), ((192483137295561951 : ℚ) / (1600990824895000000 : ℚ)), ((7434851016237748613 : ℚ) / (78905976369825000000 : ℚ)), ((2463990788371170261 : ℚ) / (26301992123275000000 : ℚ)), ((3521061934473174037 : ℚ) / (50212894053525000000 : ℚ)), ((2339904060189041583 : ℚ) / (66950525404700000000 : ℚ)), ((6705908372942755379 : ℚ) / (200851576214100000000 : ℚ)), ((6596735935325442659 : ℚ) / (200851576214100000000 : ℚ)), ((2308153772106861209 : ℚ) / (77070953663550000000 : ℚ))],
    jensenBound := ((1105428635701076994223449460199805695284963793647293325794148600942783144296296807424666194751448186413171621536402020875999874384820712406939708046875000000000000000 : ℚ) / (28650188089543967948932054177578189061490459933900611688148974015444760447555181073092644645637826874635892234636601710458585911769422902717455041131601627520530481329789473207446607 : ℚ)),
    jensenFloorQ96 := (3056911156168 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_simplexId_before"
  err.flush

theorem geometryRow058_simplexId_read :
    geometryRowsJson058.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped058.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_vertexIds_before"
  err.flush

theorem geometryRow058_vertexIds_read :
    geometryRowsJson058.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped058.vertexIds := by decide +kernel

noncomputable def geometryRow058_physicalVolumeNumeratorChars : List Char := ['2', '5', '3', '6', '7', '8', '6', '3', '2', '0', '2', '8', '9', '0', '7', '3', '0', '4', '2', '0', '2', '0', '9', '3', '5', '5', '1', '4', '8', '1', '7', '2', '2', '7', '7']
noncomputable def geometryRow058_physicalVolumeDenominatorChars : List Char := ['5', '9', '7', '2', '2', '1', '0', '0', '6', '4', '4', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow058_physicalVolumeText : String := String.ofList (geometryRow058_physicalVolumeNumeratorChars ++ '/' :: geometryRow058_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_physicalVolume_before_field"
  err.flush

theorem geometryRow058_physicalVolume_field :
    geometryRowsJson058.getObjVal? "physical_volume" = .ok (.str geometryRow058_physicalVolumeText) := by rfl

theorem geometryRow058_physicalVolume_numerator_no_slash :
    geometryRow058_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow058_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow058_physicalVolumeNumeratorChars = some (25367863202890730420209355148172277 : Int) := by decide +kernel

theorem geometryRow058_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow058_physicalVolumeDenominatorChars = some (5972210064450000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow058_physicalVolume_denominator_nonzero : (5972210064450000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow058_physicalVolume_parse :
    parseRational geometryRow058_physicalVolumeText = .ok geometryRowsTyped058.physicalVolume :=
  original_rational_fraction_of_chars geometryRow058_physicalVolumeNumeratorChars geometryRow058_physicalVolumeDenominatorChars
    (25367863202890730420209355148172277 : Int) (5972210064450000000000000000000000000000000000000000000000000 : Int)
    geometryRow058_physicalVolume_numerator_no_slash geometryRow058_physicalVolume_numerator_parse
    geometryRow058_physicalVolume_denominator_parse geometryRow058_physicalVolume_denominator_nonzero

theorem geometryRow058_physicalVolume_read :
    rationalField geometryRowsJson058 "physical_volume" = .ok geometryRowsTyped058.physicalVolume :=
  original_rationalField_of_string geometryRowsJson058 "physical_volume" geometryRow058_physicalVolumeText
    geometryRowsTyped058.physicalVolume geometryRow058_physicalVolume_field geometryRow058_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_physicalVolume_complete"
  err.flush

noncomputable def geometryRow058_meanGapNumeratorChars : List Char := ['9', '6', '7', '0', '7', '3', '8', '9']
noncomputable def geometryRow058_meanGapDenominatorChars : List Char := ['6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow058_meanGapText : String := String.ofList (geometryRow058_meanGapNumeratorChars ++ '/' :: geometryRow058_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_meanGap_before_field"
  err.flush

theorem geometryRow058_meanGap_field :
    geometryRowsJson058.getObjVal? "mean_gap" = .ok (.str geometryRow058_meanGapText) := by rfl

theorem geometryRow058_meanGap_numerator_no_slash :
    geometryRow058_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow058_meanGap_numerator_parse :
    SourceJson.intChars geometryRow058_meanGapNumeratorChars = some (96707389 : Int) := by decide +kernel

theorem geometryRow058_meanGap_denominator_parse :
    SourceJson.intChars geometryRow058_meanGapDenominatorChars = some (66220000000 : Int) := by decide +kernel

theorem geometryRow058_meanGap_denominator_nonzero : (66220000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow058_meanGap_parse :
    parseRational geometryRow058_meanGapText = .ok geometryRowsTyped058.meanGap :=
  original_rational_fraction_of_chars geometryRow058_meanGapNumeratorChars geometryRow058_meanGapDenominatorChars
    (96707389 : Int) (66220000000 : Int)
    geometryRow058_meanGap_numerator_no_slash geometryRow058_meanGap_numerator_parse
    geometryRow058_meanGap_denominator_parse geometryRow058_meanGap_denominator_nonzero

theorem geometryRow058_meanGap_read :
    rationalField geometryRowsJson058 "mean_gap" = .ok geometryRowsTyped058.meanGap :=
  original_rationalField_of_string geometryRowsJson058 "mean_gap" geometryRow058_meanGapText
    geometryRowsTyped058.meanGap geometryRow058_meanGap_field geometryRow058_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_meanGap_complete"
  err.flush

noncomputable def geometryRow058_jensenBoundNumeratorChars : List Char := ['1', '1', '0', '5', '4', '2', '8', '6', '3', '5', '7', '0', '1', '0', '7', '6', '9', '9', '4', '2', '2', '3', '4', '4', '9', '4', '6', '0', '1', '9', '9', '8', '0', '5', '6', '9', '5', '2', '8', '4', '9', '6', '3', '7', '9', '3', '6', '4', '7', '2', '9', '3', '3', '2', '5', '7', '9', '4', '1', '4', '8', '6', '0', '0', '9', '4', '2', '7', '8', '3', '1', '4', '4', '2', '9', '6', '2', '9', '6', '8', '0', '7', '4', '2', '4', '6', '6', '6', '1', '9', '4', '7', '5', '1', '4', '4', '8', '1', '8', '6', '4', '1', '3', '1', '7', '1', '6', '2', '1', '5', '3', '6', '4', '0', '2', '0', '2', '0', '8', '7', '5', '9', '9', '9', '8', '7', '4', '3', '8', '4', '8', '2', '0', '7', '1', '2', '4', '0', '6', '9', '3', '9', '7', '0', '8', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow058_jensenBoundDenominatorChars : List Char := ['2', '8', '6', '5', '0', '1', '8', '8', '0', '8', '9', '5', '4', '3', '9', '6', '7', '9', '4', '8', '9', '3', '2', '0', '5', '4', '1', '7', '7', '5', '7', '8', '1', '8', '9', '0', '6', '1', '4', '9', '0', '4', '5', '9', '9', '3', '3', '9', '0', '0', '6', '1', '1', '6', '8', '8', '1', '4', '8', '9', '7', '4', '0', '1', '5', '4', '4', '4', '7', '6', '0', '4', '4', '7', '5', '5', '5', '1', '8', '1', '0', '7', '3', '0', '9', '2', '6', '4', '4', '6', '4', '5', '6', '3', '7', '8', '2', '6', '8', '7', '4', '6', '3', '5', '8', '9', '2', '2', '3', '4', '6', '3', '6', '6', '0', '1', '7', '1', '0', '4', '5', '8', '5', '8', '5', '9', '1', '1', '7', '6', '9', '4', '2', '2', '9', '0', '2', '7', '1', '7', '4', '5', '5', '0', '4', '1', '1', '3', '1', '6', '0', '1', '6', '2', '7', '5', '2', '0', '5', '3', '0', '4', '8', '1', '3', '2', '9', '7', '8', '9', '4', '7', '3', '2', '0', '7', '4', '4', '6', '6', '0', '7']
noncomputable def geometryRow058_jensenBoundText : String := String.ofList (geometryRow058_jensenBoundNumeratorChars ++ '/' :: geometryRow058_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_jensenBound_before_field"
  err.flush

theorem geometryRow058_jensenBound_field :
    geometryRowsJson058.getObjVal? "jensen_bound" = .ok (.str geometryRow058_jensenBoundText) := by rfl

theorem geometryRow058_jensenBound_numerator_no_slash :
    geometryRow058_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow058_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow058_jensenBoundNumeratorChars = some (1105428635701076994223449460199805695284963793647293325794148600942783144296296807424666194751448186413171621536402020875999874384820712406939708046875000000000000000 : Int) := by decide +kernel

theorem geometryRow058_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow058_jensenBoundDenominatorChars = some (28650188089543967948932054177578189061490459933900611688148974015444760447555181073092644645637826874635892234636601710458585911769422902717455041131601627520530481329789473207446607 : Int) := by decide +kernel

theorem geometryRow058_jensenBound_denominator_nonzero : (28650188089543967948932054177578189061490459933900611688148974015444760447555181073092644645637826874635892234636601710458585911769422902717455041131601627520530481329789473207446607 : Int) ≠ 0 := by decide +kernel

theorem geometryRow058_jensenBound_parse :
    parseRational geometryRow058_jensenBoundText = .ok geometryRowsTyped058.jensenBound :=
  original_rational_fraction_of_chars geometryRow058_jensenBoundNumeratorChars geometryRow058_jensenBoundDenominatorChars
    (1105428635701076994223449460199805695284963793647293325794148600942783144296296807424666194751448186413171621536402020875999874384820712406939708046875000000000000000 : Int) (28650188089543967948932054177578189061490459933900611688148974015444760447555181073092644645637826874635892234636601710458585911769422902717455041131601627520530481329789473207446607 : Int)
    geometryRow058_jensenBound_numerator_no_slash geometryRow058_jensenBound_numerator_parse
    geometryRow058_jensenBound_denominator_parse geometryRow058_jensenBound_denominator_nonzero

theorem geometryRow058_jensenBound_read :
    rationalField geometryRowsJson058 "jensen_bound" = .ok geometryRowsTyped058.jensenBound :=
  original_rationalField_of_string geometryRowsJson058 "jensen_bound" geometryRow058_jensenBoundText
    geometryRowsTyped058.jensenBound geometryRow058_jensenBound_field geometryRow058_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_factorMaxima_before"
  err.flush

theorem geometryRow058_factorMaxima_read :
    rationalArrayField geometryRowsJson058 "factor_maxima" = .ok geometryRowsTyped058.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_gapWeightedMeans_before"
  err.flush

theorem geometryRow058_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson058 "gap_weighted_means" = .ok geometryRowsTyped058.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow058_floorChars : List Char := ['3', '0', '5', '6', '9', '1', '1', '1', '5', '6', '1', '6', '8']
noncomputable def geometryRow058_floorText : String := String.ofList geometryRow058_floorChars

theorem geometryRow058_floor_text_read :
    geometryRowsJson058.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow058_floorText := by rfl

theorem geometryRow058_floor_chars_parse :
    SourceJson.intChars geometryRow058_floorChars = some (3056911156168 : Int) := by decide +kernel

theorem geometryRow058_floor_parse :
    parseInteger geometryRow058_floorText = .ok geometryRowsTyped058.jensenFloorQ96 := by
  simp only [geometryRow058_floorText, parseInteger, String.toList_ofList, geometryRow058_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_058 :
    decodeGeometryRow geometryRowsJson058 = .ok geometryRowsTyped058 :=
  original_geometryRow_of_fields geometryRowsJson058 geometryRowsTyped058 geometryRow058_floorText
    geometryRow058_simplexId_read geometryRow058_vertexIds_read
    geometryRow058_physicalVolume_read geometryRow058_meanGap_read
    geometryRow058_factorMaxima_read geometryRow058_gapWeightedMeans_read
    geometryRow058_jensenBound_read geometryRow058_floor_text_read geometryRow058_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_058_original_decoder_complete"
  err.flush

theorem geometryRow058_shape :
    geometryRowsTyped058.simplexId = 58 ∧
    geometryRowsTyped058.vertexIds.size = 9 ∧ geometryRowsTyped058.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped058.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped058.factorMaxima.size = 10 ∧ geometryRowsTyped058.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson059 : SourceJson :=
  (SimplicesBlock007.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped059 : GeometryRow :=
  { simplexId := 59,
    vertexIds := #[32, 30, 28, 27, 23, 22, 13, 8, 0],
    physicalVolume := ((187123461554660157741811262059797227 : ℚ) / (4285705561200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((16950275509 : ℚ) / (199237500000 : ℚ)), ((137707428641 : ℚ) / (1593900000000 : ℚ)), ((250353451 : ℚ) / (2079000000 : ℚ)), ((63918011119 : ℚ) / (683100000000 : ℚ)), ((63546804679 : ℚ) / (683100000000 : ℚ)), ((30999851471 : ℚ) / (434700000000 : ℚ)), ((30902840921 : ℚ) / (869400000000 : ℚ)), ((29544519341 : ℚ) / (869400000000 : ℚ)), ((29071958861 : ℚ) / (869400000000 : ℚ)), ((141027770281 : ℚ) / (4781700000000 : ℚ))],
    jensenBound := ((37424229190554878576606772178674772657138615471467013303175680756500000000000000000000 : ℚ) / (191141322221841557282617599392730693037167757033023654126867900141483875819929186431256654444404004889 : ℚ)),
    jensenFloorQ96 := (15512359534894 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_simplexId_before"
  err.flush

theorem geometryRow059_simplexId_read :
    geometryRowsJson059.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped059.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_vertexIds_before"
  err.flush

theorem geometryRow059_vertexIds_read :
    geometryRowsJson059.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped059.vertexIds := by decide +kernel

noncomputable def geometryRow059_physicalVolumeNumeratorChars : List Char := ['1', '8', '7', '1', '2', '3', '4', '6', '1', '5', '5', '4', '6', '6', '0', '1', '5', '7', '7', '4', '1', '8', '1', '1', '2', '6', '2', '0', '5', '9', '7', '9', '7', '2', '2', '7']
noncomputable def geometryRow059_physicalVolumeDenominatorChars : List Char := ['4', '2', '8', '5', '7', '0', '5', '5', '6', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow059_physicalVolumeText : String := String.ofList (geometryRow059_physicalVolumeNumeratorChars ++ '/' :: geometryRow059_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_physicalVolume_before_field"
  err.flush

theorem geometryRow059_physicalVolume_field :
    geometryRowsJson059.getObjVal? "physical_volume" = .ok (.str geometryRow059_physicalVolumeText) := by rfl

theorem geometryRow059_physicalVolume_numerator_no_slash :
    geometryRow059_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow059_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow059_physicalVolumeNumeratorChars = some (187123461554660157741811262059797227 : Int) := by decide +kernel

theorem geometryRow059_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow059_physicalVolumeDenominatorChars = some (4285705561200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow059_physicalVolume_denominator_nonzero : (4285705561200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow059_physicalVolume_parse :
    parseRational geometryRow059_physicalVolumeText = .ok geometryRowsTyped059.physicalVolume :=
  original_rational_fraction_of_chars geometryRow059_physicalVolumeNumeratorChars geometryRow059_physicalVolumeDenominatorChars
    (187123461554660157741811262059797227 : Int) (4285705561200000000000000000000000000000000000000000000000000 : Int)
    geometryRow059_physicalVolume_numerator_no_slash geometryRow059_physicalVolume_numerator_parse
    geometryRow059_physicalVolume_denominator_parse geometryRow059_physicalVolume_denominator_nonzero

theorem geometryRow059_physicalVolume_read :
    rationalField geometryRowsJson059 "physical_volume" = .ok geometryRowsTyped059.physicalVolume :=
  original_rationalField_of_string geometryRowsJson059 "physical_volume" geometryRow059_physicalVolumeText
    geometryRowsTyped059.physicalVolume geometryRow059_physicalVolume_field geometryRow059_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_physicalVolume_complete"
  err.flush

noncomputable def geometryRow059_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow059_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow059_meanGapText : String := String.ofList (geometryRow059_meanGapNumeratorChars ++ '/' :: geometryRow059_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_meanGap_before_field"
  err.flush

theorem geometryRow059_meanGap_field :
    geometryRowsJson059.getObjVal? "mean_gap" = .ok (.str geometryRow059_meanGapText) := by rfl

theorem geometryRow059_meanGap_numerator_no_slash :
    geometryRow059_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow059_meanGap_numerator_parse :
    SourceJson.intChars geometryRow059_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow059_meanGap_denominator_parse :
    SourceJson.intChars geometryRow059_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow059_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow059_meanGap_parse :
    parseRational geometryRow059_meanGapText = .ok geometryRowsTyped059.meanGap :=
  original_rational_fraction_of_chars geometryRow059_meanGapNumeratorChars geometryRow059_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow059_meanGap_numerator_no_slash geometryRow059_meanGap_numerator_parse
    geometryRow059_meanGap_denominator_parse geometryRow059_meanGap_denominator_nonzero

theorem geometryRow059_meanGap_read :
    rationalField geometryRowsJson059 "mean_gap" = .ok geometryRowsTyped059.meanGap :=
  original_rationalField_of_string geometryRowsJson059 "mean_gap" geometryRow059_meanGapText
    geometryRowsTyped059.meanGap geometryRow059_meanGap_field geometryRow059_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_meanGap_complete"
  err.flush

noncomputable def geometryRow059_jensenBoundNumeratorChars : List Char := ['3', '7', '4', '2', '4', '2', '2', '9', '1', '9', '0', '5', '5', '4', '8', '7', '8', '5', '7', '6', '6', '0', '6', '7', '7', '2', '1', '7', '8', '6', '7', '4', '7', '7', '2', '6', '5', '7', '1', '3', '8', '6', '1', '5', '4', '7', '1', '4', '6', '7', '0', '1', '3', '3', '0', '3', '1', '7', '5', '6', '8', '0', '7', '5', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow059_jensenBoundDenominatorChars : List Char := ['1', '9', '1', '1', '4', '1', '3', '2', '2', '2', '2', '1', '8', '4', '1', '5', '5', '7', '2', '8', '2', '6', '1', '7', '5', '9', '9', '3', '9', '2', '7', '3', '0', '6', '9', '3', '0', '3', '7', '1', '6', '7', '7', '5', '7', '0', '3', '3', '0', '2', '3', '6', '5', '4', '1', '2', '6', '8', '6', '7', '9', '0', '0', '1', '4', '1', '4', '8', '3', '8', '7', '5', '8', '1', '9', '9', '2', '9', '1', '8', '6', '4', '3', '1', '2', '5', '6', '6', '5', '4', '4', '4', '4', '4', '0', '4', '0', '0', '4', '8', '8', '9']
noncomputable def geometryRow059_jensenBoundText : String := String.ofList (geometryRow059_jensenBoundNumeratorChars ++ '/' :: geometryRow059_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_jensenBound_before_field"
  err.flush

theorem geometryRow059_jensenBound_field :
    geometryRowsJson059.getObjVal? "jensen_bound" = .ok (.str geometryRow059_jensenBoundText) := by rfl

theorem geometryRow059_jensenBound_numerator_no_slash :
    geometryRow059_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow059_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow059_jensenBoundNumeratorChars = some (37424229190554878576606772178674772657138615471467013303175680756500000000000000000000 : Int) := by decide +kernel

theorem geometryRow059_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow059_jensenBoundDenominatorChars = some (191141322221841557282617599392730693037167757033023654126867900141483875819929186431256654444404004889 : Int) := by decide +kernel

theorem geometryRow059_jensenBound_denominator_nonzero : (191141322221841557282617599392730693037167757033023654126867900141483875819929186431256654444404004889 : Int) ≠ 0 := by decide +kernel

theorem geometryRow059_jensenBound_parse :
    parseRational geometryRow059_jensenBoundText = .ok geometryRowsTyped059.jensenBound :=
  original_rational_fraction_of_chars geometryRow059_jensenBoundNumeratorChars geometryRow059_jensenBoundDenominatorChars
    (37424229190554878576606772178674772657138615471467013303175680756500000000000000000000 : Int) (191141322221841557282617599392730693037167757033023654126867900141483875819929186431256654444404004889 : Int)
    geometryRow059_jensenBound_numerator_no_slash geometryRow059_jensenBound_numerator_parse
    geometryRow059_jensenBound_denominator_parse geometryRow059_jensenBound_denominator_nonzero

theorem geometryRow059_jensenBound_read :
    rationalField geometryRowsJson059 "jensen_bound" = .ok geometryRowsTyped059.jensenBound :=
  original_rationalField_of_string geometryRowsJson059 "jensen_bound" geometryRow059_jensenBoundText
    geometryRowsTyped059.jensenBound geometryRow059_jensenBound_field geometryRow059_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_factorMaxima_before"
  err.flush

theorem geometryRow059_factorMaxima_read :
    rationalArrayField geometryRowsJson059 "factor_maxima" = .ok geometryRowsTyped059.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_gapWeightedMeans_before"
  err.flush

theorem geometryRow059_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson059 "gap_weighted_means" = .ok geometryRowsTyped059.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow059_floorChars : List Char := ['1', '5', '5', '1', '2', '3', '5', '9', '5', '3', '4', '8', '9', '4']
noncomputable def geometryRow059_floorText : String := String.ofList geometryRow059_floorChars

theorem geometryRow059_floor_text_read :
    geometryRowsJson059.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow059_floorText := by rfl

theorem geometryRow059_floor_chars_parse :
    SourceJson.intChars geometryRow059_floorChars = some (15512359534894 : Int) := by decide +kernel

theorem geometryRow059_floor_parse :
    parseInteger geometryRow059_floorText = .ok geometryRowsTyped059.jensenFloorQ96 := by
  simp only [geometryRow059_floorText, parseInteger, String.toList_ofList, geometryRow059_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_059 :
    decodeGeometryRow geometryRowsJson059 = .ok geometryRowsTyped059 :=
  original_geometryRow_of_fields geometryRowsJson059 geometryRowsTyped059 geometryRow059_floorText
    geometryRow059_simplexId_read geometryRow059_vertexIds_read
    geometryRow059_physicalVolume_read geometryRow059_meanGap_read
    geometryRow059_factorMaxima_read geometryRow059_gapWeightedMeans_read
    geometryRow059_jensenBound_read geometryRow059_floor_text_read geometryRow059_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_059_original_decoder_complete"
  err.flush

theorem geometryRow059_shape :
    geometryRowsTyped059.simplexId = 59 ∧
    geometryRowsTyped059.vertexIds.size = 9 ∧ geometryRowsTyped059.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped059.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped059.factorMaxima.size = 10 ∧ geometryRowsTyped059.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson060 : SourceJson :=
  (SimplicesBlock007.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped060 : GeometryRow :=
  { simplexId := 60,
    vertexIds := #[32, 30, 28, 27, 23, 22, 21, 8, 0],
    physicalVolume := ((7892451321724415438561207918377219 : ℚ) / (199644669000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((496879 : ℚ) / (5600000 : ℚ)), ((10171707 : ℚ) / (110000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((37782998509 : ℚ) / (455400000000 : ℚ)), ((38384491243 : ℚ) / (455400000000 : ℚ)), ((41393959723 : ℚ) / (341550000000 : ℚ)), ((129854367413 : ℚ) / (1366200000000 : ℚ)), ((129111954533 : ℚ) / (1366200000000 : ℚ)), ((551512909 : ℚ) / (7762500000 : ℚ)), ((2199122311 : ℚ) / (62100000000 : ℚ)), ((2102099341 : ℚ) / (62100000000 : ℚ)), ((2068345021 : ℚ) / (62100000000 : ℚ)), ((39333160283 : ℚ) / (1366200000000 : ℚ))],
    jensenBound := ((1909126554461014067006896752615158242578891036571987232144555181960000000000000000000000 : ℚ) / (10229358735503523006460257324474355934990185320825007638585645970511261555279184834899944426048822687277 : ℚ)),
    jensenFloorQ96 := (14786517202897 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_simplexId_before"
  err.flush

theorem geometryRow060_simplexId_read :
    geometryRowsJson060.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped060.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_vertexIds_before"
  err.flush

theorem geometryRow060_vertexIds_read :
    geometryRowsJson060.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped060.vertexIds := by decide +kernel

noncomputable def geometryRow060_physicalVolumeNumeratorChars : List Char := ['7', '8', '9', '2', '4', '5', '1', '3', '2', '1', '7', '2', '4', '4', '1', '5', '4', '3', '8', '5', '6', '1', '2', '0', '7', '9', '1', '8', '3', '7', '7', '2', '1', '9']
noncomputable def geometryRow060_physicalVolumeDenominatorChars : List Char := ['1', '9', '9', '6', '4', '4', '6', '6', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow060_physicalVolumeText : String := String.ofList (geometryRow060_physicalVolumeNumeratorChars ++ '/' :: geometryRow060_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_physicalVolume_before_field"
  err.flush

theorem geometryRow060_physicalVolume_field :
    geometryRowsJson060.getObjVal? "physical_volume" = .ok (.str geometryRow060_physicalVolumeText) := by rfl

theorem geometryRow060_physicalVolume_numerator_no_slash :
    geometryRow060_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow060_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow060_physicalVolumeNumeratorChars = some (7892451321724415438561207918377219 : Int) := by decide +kernel

theorem geometryRow060_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow060_physicalVolumeDenominatorChars = some (199644669000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow060_physicalVolume_denominator_nonzero : (199644669000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow060_physicalVolume_parse :
    parseRational geometryRow060_physicalVolumeText = .ok geometryRowsTyped060.physicalVolume :=
  original_rational_fraction_of_chars geometryRow060_physicalVolumeNumeratorChars geometryRow060_physicalVolumeDenominatorChars
    (7892451321724415438561207918377219 : Int) (199644669000000000000000000000000000000000000000000000000000 : Int)
    geometryRow060_physicalVolume_numerator_no_slash geometryRow060_physicalVolume_numerator_parse
    geometryRow060_physicalVolume_denominator_parse geometryRow060_physicalVolume_denominator_nonzero

theorem geometryRow060_physicalVolume_read :
    rationalField geometryRowsJson060 "physical_volume" = .ok geometryRowsTyped060.physicalVolume :=
  original_rationalField_of_string geometryRowsJson060 "physical_volume" geometryRow060_physicalVolumeText
    geometryRowsTyped060.physicalVolume geometryRow060_physicalVolume_field geometryRow060_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_physicalVolume_complete"
  err.flush

noncomputable def geometryRow060_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow060_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow060_meanGapText : String := String.ofList (geometryRow060_meanGapNumeratorChars ++ '/' :: geometryRow060_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_meanGap_before_field"
  err.flush

theorem geometryRow060_meanGap_field :
    geometryRowsJson060.getObjVal? "mean_gap" = .ok (.str geometryRow060_meanGapText) := by rfl

theorem geometryRow060_meanGap_numerator_no_slash :
    geometryRow060_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow060_meanGap_numerator_parse :
    SourceJson.intChars geometryRow060_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow060_meanGap_denominator_parse :
    SourceJson.intChars geometryRow060_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow060_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow060_meanGap_parse :
    parseRational geometryRow060_meanGapText = .ok geometryRowsTyped060.meanGap :=
  original_rational_fraction_of_chars geometryRow060_meanGapNumeratorChars geometryRow060_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow060_meanGap_numerator_no_slash geometryRow060_meanGap_numerator_parse
    geometryRow060_meanGap_denominator_parse geometryRow060_meanGap_denominator_nonzero

theorem geometryRow060_meanGap_read :
    rationalField geometryRowsJson060 "mean_gap" = .ok geometryRowsTyped060.meanGap :=
  original_rationalField_of_string geometryRowsJson060 "mean_gap" geometryRow060_meanGapText
    geometryRowsTyped060.meanGap geometryRow060_meanGap_field geometryRow060_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_meanGap_complete"
  err.flush

noncomputable def geometryRow060_jensenBoundNumeratorChars : List Char := ['1', '9', '0', '9', '1', '2', '6', '5', '5', '4', '4', '6', '1', '0', '1', '4', '0', '6', '7', '0', '0', '6', '8', '9', '6', '7', '5', '2', '6', '1', '5', '1', '5', '8', '2', '4', '2', '5', '7', '8', '8', '9', '1', '0', '3', '6', '5', '7', '1', '9', '8', '7', '2', '3', '2', '1', '4', '4', '5', '5', '5', '1', '8', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow060_jensenBoundDenominatorChars : List Char := ['1', '0', '2', '2', '9', '3', '5', '8', '7', '3', '5', '5', '0', '3', '5', '2', '3', '0', '0', '6', '4', '6', '0', '2', '5', '7', '3', '2', '4', '4', '7', '4', '3', '5', '5', '9', '3', '4', '9', '9', '0', '1', '8', '5', '3', '2', '0', '8', '2', '5', '0', '0', '7', '6', '3', '8', '5', '8', '5', '6', '4', '5', '9', '7', '0', '5', '1', '1', '2', '6', '1', '5', '5', '5', '2', '7', '9', '1', '8', '4', '8', '3', '4', '8', '9', '9', '9', '4', '4', '4', '2', '6', '0', '4', '8', '8', '2', '2', '6', '8', '7', '2', '7', '7']
noncomputable def geometryRow060_jensenBoundText : String := String.ofList (geometryRow060_jensenBoundNumeratorChars ++ '/' :: geometryRow060_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_jensenBound_before_field"
  err.flush

theorem geometryRow060_jensenBound_field :
    geometryRowsJson060.getObjVal? "jensen_bound" = .ok (.str geometryRow060_jensenBoundText) := by rfl

theorem geometryRow060_jensenBound_numerator_no_slash :
    geometryRow060_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow060_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow060_jensenBoundNumeratorChars = some (1909126554461014067006896752615158242578891036571987232144555181960000000000000000000000 : Int) := by decide +kernel

theorem geometryRow060_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow060_jensenBoundDenominatorChars = some (10229358735503523006460257324474355934990185320825007638585645970511261555279184834899944426048822687277 : Int) := by decide +kernel

theorem geometryRow060_jensenBound_denominator_nonzero : (10229358735503523006460257324474355934990185320825007638585645970511261555279184834899944426048822687277 : Int) ≠ 0 := by decide +kernel

theorem geometryRow060_jensenBound_parse :
    parseRational geometryRow060_jensenBoundText = .ok geometryRowsTyped060.jensenBound :=
  original_rational_fraction_of_chars geometryRow060_jensenBoundNumeratorChars geometryRow060_jensenBoundDenominatorChars
    (1909126554461014067006896752615158242578891036571987232144555181960000000000000000000000 : Int) (10229358735503523006460257324474355934990185320825007638585645970511261555279184834899944426048822687277 : Int)
    geometryRow060_jensenBound_numerator_no_slash geometryRow060_jensenBound_numerator_parse
    geometryRow060_jensenBound_denominator_parse geometryRow060_jensenBound_denominator_nonzero

theorem geometryRow060_jensenBound_read :
    rationalField geometryRowsJson060 "jensen_bound" = .ok geometryRowsTyped060.jensenBound :=
  original_rationalField_of_string geometryRowsJson060 "jensen_bound" geometryRow060_jensenBoundText
    geometryRowsTyped060.jensenBound geometryRow060_jensenBound_field geometryRow060_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_factorMaxima_before"
  err.flush

theorem geometryRow060_factorMaxima_read :
    rationalArrayField geometryRowsJson060 "factor_maxima" = .ok geometryRowsTyped060.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_gapWeightedMeans_before"
  err.flush

theorem geometryRow060_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson060 "gap_weighted_means" = .ok geometryRowsTyped060.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow060_floorChars : List Char := ['1', '4', '7', '8', '6', '5', '1', '7', '2', '0', '2', '8', '9', '7']
noncomputable def geometryRow060_floorText : String := String.ofList geometryRow060_floorChars

theorem geometryRow060_floor_text_read :
    geometryRowsJson060.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow060_floorText := by rfl

theorem geometryRow060_floor_chars_parse :
    SourceJson.intChars geometryRow060_floorChars = some (14786517202897 : Int) := by decide +kernel

theorem geometryRow060_floor_parse :
    parseInteger geometryRow060_floorText = .ok geometryRowsTyped060.jensenFloorQ96 := by
  simp only [geometryRow060_floorText, parseInteger, String.toList_ofList, geometryRow060_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_060 :
    decodeGeometryRow geometryRowsJson060 = .ok geometryRowsTyped060 :=
  original_geometryRow_of_fields geometryRowsJson060 geometryRowsTyped060 geometryRow060_floorText
    geometryRow060_simplexId_read geometryRow060_vertexIds_read
    geometryRow060_physicalVolume_read geometryRow060_meanGap_read
    geometryRow060_factorMaxima_read geometryRow060_gapWeightedMeans_read
    geometryRow060_jensenBound_read geometryRow060_floor_text_read geometryRow060_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_060_original_decoder_complete"
  err.flush

theorem geometryRow060_shape :
    geometryRowsTyped060.simplexId = 60 ∧
    geometryRowsTyped060.vertexIds.size = 9 ∧ geometryRowsTyped060.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped060.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped060.factorMaxima.size = 10 ∧ geometryRowsTyped060.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson061 : SourceJson :=
  (SimplicesBlock007.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped061 : GeometryRow :=
  { simplexId := 61,
    vertexIds := #[32, 30, 28, 26, 14, 4, 3, 1, 0],
    physicalVolume := ((4780252292834862346910196216916239294643 : ℚ) / (2681133865622553600000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1544234459 : ℚ) / (521482500000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((32031 : ℚ) / (418750 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((34387634314098720688527493 : ℚ) / (397105219358427333600000000 : ℚ)), ((2550757926030458318545541 : ℚ) / (28364658525601952400000000 : ℚ)), ((9291827443960867161324967 : ℚ) / (79421043871685466720000000 : ℚ)), ((4102955973497122248299691 : ℚ) / (44122802150936370400000000 : ℚ)), ((12236937010042208059248193 : ℚ) / (132368406452809111200000000 : ℚ)), ((2569519453428016426277033 : ℚ) / (36100474487129757600000000 : ℚ)), ((2601256901333896131826163 : ℚ) / (72200948974259515200000000 : ℚ)), ((40546302236366314282763 : ℚ) / (1183622114332123200000000 : ℚ)), ((1188741512972390210497159 : ℚ) / (36100474487129757600000000 : ℚ)), ((869948640673167426343927 : ℚ) / (28364658525601952400000000 : ℚ))],
    jensenBound := ((10562759716502976314918133962179202756305837159213934489043043403847445088609707874489002098557080711710543378092699183589430859028748243219846572513623704906386506123786074940277730164590928260804766597120000000000000000000000000 : ℚ) / (347532779632375517765558342107664497747201028319880571085331008837642489617968887579935721775001755712744471813166205616953048629609166607429780746473783343613802188664274837047418435764909585696846242681087174350850486367999620474588631856541 : ℚ)),
    jensenFloorQ96 := (2408026213537243 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_simplexId_before"
  err.flush

theorem geometryRow061_simplexId_read :
    geometryRowsJson061.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped061.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_vertexIds_before"
  err.flush

theorem geometryRow061_vertexIds_read :
    geometryRowsJson061.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped061.vertexIds := by decide +kernel

noncomputable def geometryRow061_physicalVolumeNumeratorChars : List Char := ['4', '7', '8', '0', '2', '5', '2', '2', '9', '2', '8', '3', '4', '8', '6', '2', '3', '4', '6', '9', '1', '0', '1', '9', '6', '2', '1', '6', '9', '1', '6', '2', '3', '9', '2', '9', '4', '6', '4', '3']
noncomputable def geometryRow061_physicalVolumeDenominatorChars : List Char := ['2', '6', '8', '1', '1', '3', '3', '8', '6', '5', '6', '2', '2', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow061_physicalVolumeText : String := String.ofList (geometryRow061_physicalVolumeNumeratorChars ++ '/' :: geometryRow061_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_physicalVolume_before_field"
  err.flush

theorem geometryRow061_physicalVolume_field :
    geometryRowsJson061.getObjVal? "physical_volume" = .ok (.str geometryRow061_physicalVolumeText) := by rfl

theorem geometryRow061_physicalVolume_numerator_no_slash :
    geometryRow061_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow061_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow061_physicalVolumeNumeratorChars = some (4780252292834862346910196216916239294643 : Int) := by decide +kernel

theorem geometryRow061_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow061_physicalVolumeDenominatorChars = some (2681133865622553600000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow061_physicalVolume_denominator_nonzero : (2681133865622553600000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow061_physicalVolume_parse :
    parseRational geometryRow061_physicalVolumeText = .ok geometryRowsTyped061.physicalVolume :=
  original_rational_fraction_of_chars geometryRow061_physicalVolumeNumeratorChars geometryRow061_physicalVolumeDenominatorChars
    (4780252292834862346910196216916239294643 : Int) (2681133865622553600000000000000000000000000000000000000000000000 : Int)
    geometryRow061_physicalVolume_numerator_no_slash geometryRow061_physicalVolume_numerator_parse
    geometryRow061_physicalVolume_denominator_parse geometryRow061_physicalVolume_denominator_nonzero

theorem geometryRow061_physicalVolume_read :
    rationalField geometryRowsJson061 "physical_volume" = .ok geometryRowsTyped061.physicalVolume :=
  original_rationalField_of_string geometryRowsJson061 "physical_volume" geometryRow061_physicalVolumeText
    geometryRowsTyped061.physicalVolume geometryRow061_physicalVolume_field geometryRow061_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_physicalVolume_complete"
  err.flush

noncomputable def geometryRow061_meanGapNumeratorChars : List Char := ['1', '5', '4', '4', '2', '3', '4', '4', '5', '9']
noncomputable def geometryRow061_meanGapDenominatorChars : List Char := ['5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0']
noncomputable def geometryRow061_meanGapText : String := String.ofList (geometryRow061_meanGapNumeratorChars ++ '/' :: geometryRow061_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_meanGap_before_field"
  err.flush

theorem geometryRow061_meanGap_field :
    geometryRowsJson061.getObjVal? "mean_gap" = .ok (.str geometryRow061_meanGapText) := by rfl

theorem geometryRow061_meanGap_numerator_no_slash :
    geometryRow061_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow061_meanGap_numerator_parse :
    SourceJson.intChars geometryRow061_meanGapNumeratorChars = some (1544234459 : Int) := by decide +kernel

theorem geometryRow061_meanGap_denominator_parse :
    SourceJson.intChars geometryRow061_meanGapDenominatorChars = some (521482500000 : Int) := by decide +kernel

theorem geometryRow061_meanGap_denominator_nonzero : (521482500000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow061_meanGap_parse :
    parseRational geometryRow061_meanGapText = .ok geometryRowsTyped061.meanGap :=
  original_rational_fraction_of_chars geometryRow061_meanGapNumeratorChars geometryRow061_meanGapDenominatorChars
    (1544234459 : Int) (521482500000 : Int)
    geometryRow061_meanGap_numerator_no_slash geometryRow061_meanGap_numerator_parse
    geometryRow061_meanGap_denominator_parse geometryRow061_meanGap_denominator_nonzero

theorem geometryRow061_meanGap_read :
    rationalField geometryRowsJson061 "mean_gap" = .ok geometryRowsTyped061.meanGap :=
  original_rationalField_of_string geometryRowsJson061 "mean_gap" geometryRow061_meanGapText
    geometryRowsTyped061.meanGap geometryRow061_meanGap_field geometryRow061_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_meanGap_complete"
  err.flush

noncomputable def geometryRow061_jensenBoundNumeratorChars : List Char := ['1', '0', '5', '6', '2', '7', '5', '9', '7', '1', '6', '5', '0', '2', '9', '7', '6', '3', '1', '4', '9', '1', '8', '1', '3', '3', '9', '6', '2', '1', '7', '9', '2', '0', '2', '7', '5', '6', '3', '0', '5', '8', '3', '7', '1', '5', '9', '2', '1', '3', '9', '3', '4', '4', '8', '9', '0', '4', '3', '0', '4', '3', '4', '0', '3', '8', '4', '7', '4', '4', '5', '0', '8', '8', '6', '0', '9', '7', '0', '7', '8', '7', '4', '4', '8', '9', '0', '0', '2', '0', '9', '8', '5', '5', '7', '0', '8', '0', '7', '1', '1', '7', '1', '0', '5', '4', '3', '3', '7', '8', '0', '9', '2', '6', '9', '9', '1', '8', '3', '5', '8', '9', '4', '3', '0', '8', '5', '9', '0', '2', '8', '7', '4', '8', '2', '4', '3', '2', '1', '9', '8', '4', '6', '5', '7', '2', '5', '1', '3', '6', '2', '3', '7', '0', '4', '9', '0', '6', '3', '8', '6', '5', '0', '6', '1', '2', '3', '7', '8', '6', '0', '7', '4', '9', '4', '0', '2', '7', '7', '7', '3', '0', '1', '6', '4', '5', '9', '0', '9', '2', '8', '2', '6', '0', '8', '0', '4', '7', '6', '6', '5', '9', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow061_jensenBoundDenominatorChars : List Char := ['3', '4', '7', '5', '3', '2', '7', '7', '9', '6', '3', '2', '3', '7', '5', '5', '1', '7', '7', '6', '5', '5', '5', '8', '3', '4', '2', '1', '0', '7', '6', '6', '4', '4', '9', '7', '7', '4', '7', '2', '0', '1', '0', '2', '8', '3', '1', '9', '8', '8', '0', '5', '7', '1', '0', '8', '5', '3', '3', '1', '0', '0', '8', '8', '3', '7', '6', '4', '2', '4', '8', '9', '6', '1', '7', '9', '6', '8', '8', '8', '7', '5', '7', '9', '9', '3', '5', '7', '2', '1', '7', '7', '5', '0', '0', '1', '7', '5', '5', '7', '1', '2', '7', '4', '4', '4', '7', '1', '8', '1', '3', '1', '6', '6', '2', '0', '5', '6', '1', '6', '9', '5', '3', '0', '4', '8', '6', '2', '9', '6', '0', '9', '1', '6', '6', '6', '0', '7', '4', '2', '9', '7', '8', '0', '7', '4', '6', '4', '7', '3', '7', '8', '3', '3', '4', '3', '6', '1', '3', '8', '0', '2', '1', '8', '8', '6', '6', '4', '2', '7', '4', '8', '3', '7', '0', '4', '7', '4', '1', '8', '4', '3', '5', '7', '6', '4', '9', '0', '9', '5', '8', '5', '6', '9', '6', '8', '4', '6', '2', '4', '2', '6', '8', '1', '0', '8', '7', '1', '7', '4', '3', '5', '0', '8', '5', '0', '4', '8', '6', '3', '6', '7', '9', '9', '9', '6', '2', '0', '4', '7', '4', '5', '8', '8', '6', '3', '1', '8', '5', '6', '5', '4', '1']
noncomputable def geometryRow061_jensenBoundText : String := String.ofList (geometryRow061_jensenBoundNumeratorChars ++ '/' :: geometryRow061_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_jensenBound_before_field"
  err.flush

theorem geometryRow061_jensenBound_field :
    geometryRowsJson061.getObjVal? "jensen_bound" = .ok (.str geometryRow061_jensenBoundText) := by rfl

theorem geometryRow061_jensenBound_numerator_no_slash :
    geometryRow061_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow061_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow061_jensenBoundNumeratorChars = some (10562759716502976314918133962179202756305837159213934489043043403847445088609707874489002098557080711710543378092699183589430859028748243219846572513623704906386506123786074940277730164590928260804766597120000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow061_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow061_jensenBoundDenominatorChars = some (347532779632375517765558342107664497747201028319880571085331008837642489617968887579935721775001755712744471813166205616953048629609166607429780746473783343613802188664274837047418435764909585696846242681087174350850486367999620474588631856541 : Int) := by decide +kernel

theorem geometryRow061_jensenBound_denominator_nonzero : (347532779632375517765558342107664497747201028319880571085331008837642489617968887579935721775001755712744471813166205616953048629609166607429780746473783343613802188664274837047418435764909585696846242681087174350850486367999620474588631856541 : Int) ≠ 0 := by decide +kernel

theorem geometryRow061_jensenBound_parse :
    parseRational geometryRow061_jensenBoundText = .ok geometryRowsTyped061.jensenBound :=
  original_rational_fraction_of_chars geometryRow061_jensenBoundNumeratorChars geometryRow061_jensenBoundDenominatorChars
    (10562759716502976314918133962179202756305837159213934489043043403847445088609707874489002098557080711710543378092699183589430859028748243219846572513623704906386506123786074940277730164590928260804766597120000000000000000000000000 : Int) (347532779632375517765558342107664497747201028319880571085331008837642489617968887579935721775001755712744471813166205616953048629609166607429780746473783343613802188664274837047418435764909585696846242681087174350850486367999620474588631856541 : Int)
    geometryRow061_jensenBound_numerator_no_slash geometryRow061_jensenBound_numerator_parse
    geometryRow061_jensenBound_denominator_parse geometryRow061_jensenBound_denominator_nonzero

theorem geometryRow061_jensenBound_read :
    rationalField geometryRowsJson061 "jensen_bound" = .ok geometryRowsTyped061.jensenBound :=
  original_rationalField_of_string geometryRowsJson061 "jensen_bound" geometryRow061_jensenBoundText
    geometryRowsTyped061.jensenBound geometryRow061_jensenBound_field geometryRow061_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_factorMaxima_before"
  err.flush

theorem geometryRow061_factorMaxima_read :
    rationalArrayField geometryRowsJson061 "factor_maxima" = .ok geometryRowsTyped061.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_gapWeightedMeans_before"
  err.flush

theorem geometryRow061_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson061 "gap_weighted_means" = .ok geometryRowsTyped061.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow061_floorChars : List Char := ['2', '4', '0', '8', '0', '2', '6', '2', '1', '3', '5', '3', '7', '2', '4', '3']
noncomputable def geometryRow061_floorText : String := String.ofList geometryRow061_floorChars

theorem geometryRow061_floor_text_read :
    geometryRowsJson061.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow061_floorText := by rfl

theorem geometryRow061_floor_chars_parse :
    SourceJson.intChars geometryRow061_floorChars = some (2408026213537243 : Int) := by decide +kernel

theorem geometryRow061_floor_parse :
    parseInteger geometryRow061_floorText = .ok geometryRowsTyped061.jensenFloorQ96 := by
  simp only [geometryRow061_floorText, parseInteger, String.toList_ofList, geometryRow061_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_061 :
    decodeGeometryRow geometryRowsJson061 = .ok geometryRowsTyped061 :=
  original_geometryRow_of_fields geometryRowsJson061 geometryRowsTyped061 geometryRow061_floorText
    geometryRow061_simplexId_read geometryRow061_vertexIds_read
    geometryRow061_physicalVolume_read geometryRow061_meanGap_read
    geometryRow061_factorMaxima_read geometryRow061_gapWeightedMeans_read
    geometryRow061_jensenBound_read geometryRow061_floor_text_read geometryRow061_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_061_original_decoder_complete"
  err.flush

theorem geometryRow061_shape :
    geometryRowsTyped061.simplexId = 61 ∧
    geometryRowsTyped061.vertexIds.size = 9 ∧ geometryRowsTyped061.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped061.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped061.factorMaxima.size = 10 ∧ geometryRowsTyped061.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson062 : SourceJson :=
  (SimplicesBlock007.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped062 : GeometryRow :=
  { simplexId := 62,
    vertexIds := #[32, 30, 28, 26, 14, 12, 3, 1, 0],
    physicalVolume := ((126667460419650364817724874448353837729 : ℚ) / (8313593381775360000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((24277423 : ℚ) / (10864218750 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((8715162462384042518957231 : ℚ) / (99888369460325107200000000 : ℚ)), ((641644899224658908314987 : ℚ) / (7134883532880364800000000 : ℚ)), ((2345719141651523193866489 : ℚ) / (19977673892065021440000000 : ℚ)), ((3066941290514979576576391 : ℚ) / (33296123153441702400000000 : ℚ)), ((1016282564880296628440877 : ℚ) / (11098707717813900800000000 : ℚ)), ((654923498333761350050311 : ℚ) / (9080760860029555200000000 : ℚ)), ((680764682521852235317201 : ℚ) / (18161521720059110400000000 : ℚ)), ((612868572388369312880701 : ℚ) / (18161521720059110400000000 : ℚ)), ((294235586215111498690133 : ℚ) / (9080760860029555200000000 : ℚ)), ((218835990498140163194489 : ℚ) / (7134883532880364800000000 : ℚ))],
    jensenBound := ((46351922812719436904800015618333322445401995218936654181486610743924432606432314283866586574935515234093039024566010864551957917139430722920312164468885691444461105100371361746799220251736089051948646400000000000000000000000000 : ℚ) / (239780474704748687839590644452471659906843769252978076566505309950649443982636495276397948813830444479828186137376718204113471167717924040218059181929323911998193484844050377784121707969967357486914233292123808261073441145045109880460658939 : ℚ)),
    jensenFloorQ96 := (15315582630223407 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_simplexId_before"
  err.flush

theorem geometryRow062_simplexId_read :
    geometryRowsJson062.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped062.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_vertexIds_before"
  err.flush

theorem geometryRow062_vertexIds_read :
    geometryRowsJson062.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped062.vertexIds := by decide +kernel

noncomputable def geometryRow062_physicalVolumeNumeratorChars : List Char := ['1', '2', '6', '6', '6', '7', '4', '6', '0', '4', '1', '9', '6', '5', '0', '3', '6', '4', '8', '1', '7', '7', '2', '4', '8', '7', '4', '4', '4', '8', '3', '5', '3', '8', '3', '7', '7', '2', '9']
noncomputable def geometryRow062_physicalVolumeDenominatorChars : List Char := ['8', '3', '1', '3', '5', '9', '3', '3', '8', '1', '7', '7', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow062_physicalVolumeText : String := String.ofList (geometryRow062_physicalVolumeNumeratorChars ++ '/' :: geometryRow062_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_physicalVolume_before_field"
  err.flush

theorem geometryRow062_physicalVolume_field :
    geometryRowsJson062.getObjVal? "physical_volume" = .ok (.str geometryRow062_physicalVolumeText) := by rfl

theorem geometryRow062_physicalVolume_numerator_no_slash :
    geometryRow062_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow062_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow062_physicalVolumeNumeratorChars = some (126667460419650364817724874448353837729 : Int) := by decide +kernel

theorem geometryRow062_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow062_physicalVolumeDenominatorChars = some (8313593381775360000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow062_physicalVolume_denominator_nonzero : (8313593381775360000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow062_physicalVolume_parse :
    parseRational geometryRow062_physicalVolumeText = .ok geometryRowsTyped062.physicalVolume :=
  original_rational_fraction_of_chars geometryRow062_physicalVolumeNumeratorChars geometryRow062_physicalVolumeDenominatorChars
    (126667460419650364817724874448353837729 : Int) (8313593381775360000000000000000000000000000000000000000000000 : Int)
    geometryRow062_physicalVolume_numerator_no_slash geometryRow062_physicalVolume_numerator_parse
    geometryRow062_physicalVolume_denominator_parse geometryRow062_physicalVolume_denominator_nonzero

theorem geometryRow062_physicalVolume_read :
    rationalField geometryRowsJson062 "physical_volume" = .ok geometryRowsTyped062.physicalVolume :=
  original_rationalField_of_string geometryRowsJson062 "physical_volume" geometryRow062_physicalVolumeText
    geometryRowsTyped062.physicalVolume geometryRow062_physicalVolume_field geometryRow062_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_physicalVolume_complete"
  err.flush

noncomputable def geometryRow062_meanGapNumeratorChars : List Char := ['2', '4', '2', '7', '7', '4', '2', '3']
noncomputable def geometryRow062_meanGapDenominatorChars : List Char := ['1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0']
noncomputable def geometryRow062_meanGapText : String := String.ofList (geometryRow062_meanGapNumeratorChars ++ '/' :: geometryRow062_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_meanGap_before_field"
  err.flush

theorem geometryRow062_meanGap_field :
    geometryRowsJson062.getObjVal? "mean_gap" = .ok (.str geometryRow062_meanGapText) := by rfl

theorem geometryRow062_meanGap_numerator_no_slash :
    geometryRow062_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow062_meanGap_numerator_parse :
    SourceJson.intChars geometryRow062_meanGapNumeratorChars = some (24277423 : Int) := by decide +kernel

theorem geometryRow062_meanGap_denominator_parse :
    SourceJson.intChars geometryRow062_meanGapDenominatorChars = some (10864218750 : Int) := by decide +kernel

theorem geometryRow062_meanGap_denominator_nonzero : (10864218750 : Int) ≠ 0 := by decide +kernel

theorem geometryRow062_meanGap_parse :
    parseRational geometryRow062_meanGapText = .ok geometryRowsTyped062.meanGap :=
  original_rational_fraction_of_chars geometryRow062_meanGapNumeratorChars geometryRow062_meanGapDenominatorChars
    (24277423 : Int) (10864218750 : Int)
    geometryRow062_meanGap_numerator_no_slash geometryRow062_meanGap_numerator_parse
    geometryRow062_meanGap_denominator_parse geometryRow062_meanGap_denominator_nonzero

theorem geometryRow062_meanGap_read :
    rationalField geometryRowsJson062 "mean_gap" = .ok geometryRowsTyped062.meanGap :=
  original_rationalField_of_string geometryRowsJson062 "mean_gap" geometryRow062_meanGapText
    geometryRowsTyped062.meanGap geometryRow062_meanGap_field geometryRow062_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_meanGap_complete"
  err.flush

noncomputable def geometryRow062_jensenBoundNumeratorChars : List Char := ['4', '6', '3', '5', '1', '9', '2', '2', '8', '1', '2', '7', '1', '9', '4', '3', '6', '9', '0', '4', '8', '0', '0', '0', '1', '5', '6', '1', '8', '3', '3', '3', '3', '2', '2', '4', '4', '5', '4', '0', '1', '9', '9', '5', '2', '1', '8', '9', '3', '6', '6', '5', '4', '1', '8', '1', '4', '8', '6', '6', '1', '0', '7', '4', '3', '9', '2', '4', '4', '3', '2', '6', '0', '6', '4', '3', '2', '3', '1', '4', '2', '8', '3', '8', '6', '6', '5', '8', '6', '5', '7', '4', '9', '3', '5', '5', '1', '5', '2', '3', '4', '0', '9', '3', '0', '3', '9', '0', '2', '4', '5', '6', '6', '0', '1', '0', '8', '6', '4', '5', '5', '1', '9', '5', '7', '9', '1', '7', '1', '3', '9', '4', '3', '0', '7', '2', '2', '9', '2', '0', '3', '1', '2', '1', '6', '4', '4', '6', '8', '8', '8', '5', '6', '9', '1', '4', '4', '4', '4', '6', '1', '1', '0', '5', '1', '0', '0', '3', '7', '1', '3', '6', '1', '7', '4', '6', '7', '9', '9', '2', '2', '0', '2', '5', '1', '7', '3', '6', '0', '8', '9', '0', '5', '1', '9', '4', '8', '6', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow062_jensenBoundDenominatorChars : List Char := ['2', '3', '9', '7', '8', '0', '4', '7', '4', '7', '0', '4', '7', '4', '8', '6', '8', '7', '8', '3', '9', '5', '9', '0', '6', '4', '4', '4', '5', '2', '4', '7', '1', '6', '5', '9', '9', '0', '6', '8', '4', '3', '7', '6', '9', '2', '5', '2', '9', '7', '8', '0', '7', '6', '5', '6', '6', '5', '0', '5', '3', '0', '9', '9', '5', '0', '6', '4', '9', '4', '4', '3', '9', '8', '2', '6', '3', '6', '4', '9', '5', '2', '7', '6', '3', '9', '7', '9', '4', '8', '8', '1', '3', '8', '3', '0', '4', '4', '4', '4', '7', '9', '8', '2', '8', '1', '8', '6', '1', '3', '7', '3', '7', '6', '7', '1', '8', '2', '0', '4', '1', '1', '3', '4', '7', '1', '1', '6', '7', '7', '1', '7', '9', '2', '4', '0', '4', '0', '2', '1', '8', '0', '5', '9', '1', '8', '1', '9', '2', '9', '3', '2', '3', '9', '1', '1', '9', '9', '8', '1', '9', '3', '4', '8', '4', '8', '4', '4', '0', '5', '0', '3', '7', '7', '7', '8', '4', '1', '2', '1', '7', '0', '7', '9', '6', '9', '9', '6', '7', '3', '5', '7', '4', '8', '6', '9', '1', '4', '2', '3', '3', '2', '9', '2', '1', '2', '3', '8', '0', '8', '2', '6', '1', '0', '7', '3', '4', '4', '1', '1', '4', '5', '0', '4', '5', '1', '0', '9', '8', '8', '0', '4', '6', '0', '6', '5', '8', '9', '3', '9']
noncomputable def geometryRow062_jensenBoundText : String := String.ofList (geometryRow062_jensenBoundNumeratorChars ++ '/' :: geometryRow062_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_jensenBound_before_field"
  err.flush

theorem geometryRow062_jensenBound_field :
    geometryRowsJson062.getObjVal? "jensen_bound" = .ok (.str geometryRow062_jensenBoundText) := by rfl

theorem geometryRow062_jensenBound_numerator_no_slash :
    geometryRow062_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow062_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow062_jensenBoundNumeratorChars = some (46351922812719436904800015618333322445401995218936654181486610743924432606432314283866586574935515234093039024566010864551957917139430722920312164468885691444461105100371361746799220251736089051948646400000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow062_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow062_jensenBoundDenominatorChars = some (239780474704748687839590644452471659906843769252978076566505309950649443982636495276397948813830444479828186137376718204113471167717924040218059181929323911998193484844050377784121707969967357486914233292123808261073441145045109880460658939 : Int) := by decide +kernel

theorem geometryRow062_jensenBound_denominator_nonzero : (239780474704748687839590644452471659906843769252978076566505309950649443982636495276397948813830444479828186137376718204113471167717924040218059181929323911998193484844050377784121707969967357486914233292123808261073441145045109880460658939 : Int) ≠ 0 := by decide +kernel

theorem geometryRow062_jensenBound_parse :
    parseRational geometryRow062_jensenBoundText = .ok geometryRowsTyped062.jensenBound :=
  original_rational_fraction_of_chars geometryRow062_jensenBoundNumeratorChars geometryRow062_jensenBoundDenominatorChars
    (46351922812719436904800015618333322445401995218936654181486610743924432606432314283866586574935515234093039024566010864551957917139430722920312164468885691444461105100371361746799220251736089051948646400000000000000000000000000 : Int) (239780474704748687839590644452471659906843769252978076566505309950649443982636495276397948813830444479828186137376718204113471167717924040218059181929323911998193484844050377784121707969967357486914233292123808261073441145045109880460658939 : Int)
    geometryRow062_jensenBound_numerator_no_slash geometryRow062_jensenBound_numerator_parse
    geometryRow062_jensenBound_denominator_parse geometryRow062_jensenBound_denominator_nonzero

theorem geometryRow062_jensenBound_read :
    rationalField geometryRowsJson062 "jensen_bound" = .ok geometryRowsTyped062.jensenBound :=
  original_rationalField_of_string geometryRowsJson062 "jensen_bound" geometryRow062_jensenBoundText
    geometryRowsTyped062.jensenBound geometryRow062_jensenBound_field geometryRow062_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_factorMaxima_before"
  err.flush

theorem geometryRow062_factorMaxima_read :
    rationalArrayField geometryRowsJson062 "factor_maxima" = .ok geometryRowsTyped062.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_gapWeightedMeans_before"
  err.flush

theorem geometryRow062_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson062 "gap_weighted_means" = .ok geometryRowsTyped062.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow062_floorChars : List Char := ['1', '5', '3', '1', '5', '5', '8', '2', '6', '3', '0', '2', '2', '3', '4', '0', '7']
noncomputable def geometryRow062_floorText : String := String.ofList geometryRow062_floorChars

theorem geometryRow062_floor_text_read :
    geometryRowsJson062.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow062_floorText := by rfl

theorem geometryRow062_floor_chars_parse :
    SourceJson.intChars geometryRow062_floorChars = some (15315582630223407 : Int) := by decide +kernel

theorem geometryRow062_floor_parse :
    parseInteger geometryRow062_floorText = .ok geometryRowsTyped062.jensenFloorQ96 := by
  simp only [geometryRow062_floorText, parseInteger, String.toList_ofList, geometryRow062_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_062 :
    decodeGeometryRow geometryRowsJson062 = .ok geometryRowsTyped062 :=
  original_geometryRow_of_fields geometryRowsJson062 geometryRowsTyped062 geometryRow062_floorText
    geometryRow062_simplexId_read geometryRow062_vertexIds_read
    geometryRow062_physicalVolume_read geometryRow062_meanGap_read
    geometryRow062_factorMaxima_read geometryRow062_gapWeightedMeans_read
    geometryRow062_jensenBound_read geometryRow062_floor_text_read geometryRow062_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_062_original_decoder_complete"
  err.flush

theorem geometryRow062_shape :
    geometryRowsTyped062.simplexId = 62 ∧
    geometryRowsTyped062.vertexIds.size = 9 ∧ geometryRowsTyped062.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped062.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped062.factorMaxima.size = 10 ∧ geometryRowsTyped062.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson063 : SourceJson :=
  (SimplicesBlock007.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped063 : GeometryRow :=
  { simplexId := 63,
    vertexIds := #[32, 30, 28, 26, 14, 12, 10, 1, 0],
    physicalVolume := ((9645739089426171296254897166510507 : ℚ) / (1812556696608000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((587407753616025732337 : ℚ) / (6698288083509618750000 : ℚ)), ((1373189525622930835423 : ℚ) / (15310372762307700000000 : ℚ)), ((5051463193314546359039 : ℚ) / (42869043734461560000000 : ℚ)), ((2172877690269424396593 : ℚ) / (23816135408034200000000 : ℚ)), ((6479806971381947661539 : ℚ) / (71448406224102600000000 : ℚ)), ((1423988964840638255749 : ℚ) / (19485928970209800000000 : ℚ)), ((759025713054871116077 : ℚ) / (19485928970209800000000 : ℚ)), ((10118236598477240063 : ℚ) / (304467640159528125000 : ℚ)), ((19574052455759389381 : ℚ) / (608935280319056250000 : ℚ)), ((468361137900119525981 : ℚ) / (15310372762307700000000 : ℚ))],
    jensenBound := ((24133961874626308185809101252755883823656959241730795882010197671612110277434809565682150661990773021331288773666188532933221592280390974647472354969288054998913351196777343750000000000000 : ℚ) / (547334533509429380767290805663073837046938595605057995840350593387855426460278631527282851885628474973490183134482650643797304022325212893636220510394753682631575340100948073556423671086618131807500445313 : ℚ)),
    jensenFloorQ96 := (3493456627441 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_simplexId_before"
  err.flush

theorem geometryRow063_simplexId_read :
    geometryRowsJson063.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped063.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_vertexIds_before"
  err.flush

theorem geometryRow063_vertexIds_read :
    geometryRowsJson063.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped063.vertexIds := by decide +kernel

noncomputable def geometryRow063_physicalVolumeNumeratorChars : List Char := ['9', '6', '4', '5', '7', '3', '9', '0', '8', '9', '4', '2', '6', '1', '7', '1', '2', '9', '6', '2', '5', '4', '8', '9', '7', '1', '6', '6', '5', '1', '0', '5', '0', '7']
noncomputable def geometryRow063_physicalVolumeDenominatorChars : List Char := ['1', '8', '1', '2', '5', '5', '6', '6', '9', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow063_physicalVolumeText : String := String.ofList (geometryRow063_physicalVolumeNumeratorChars ++ '/' :: geometryRow063_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_physicalVolume_before_field"
  err.flush

theorem geometryRow063_physicalVolume_field :
    geometryRowsJson063.getObjVal? "physical_volume" = .ok (.str geometryRow063_physicalVolumeText) := by rfl

theorem geometryRow063_physicalVolume_numerator_no_slash :
    geometryRow063_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow063_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow063_physicalVolumeNumeratorChars = some (9645739089426171296254897166510507 : Int) := by decide +kernel

theorem geometryRow063_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow063_physicalVolumeDenominatorChars = some (1812556696608000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow063_physicalVolume_denominator_nonzero : (1812556696608000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow063_physicalVolume_parse :
    parseRational geometryRow063_physicalVolumeText = .ok geometryRowsTyped063.physicalVolume :=
  original_rational_fraction_of_chars geometryRow063_physicalVolumeNumeratorChars geometryRow063_physicalVolumeDenominatorChars
    (9645739089426171296254897166510507 : Int) (1812556696608000000000000000000000000000000000000000000000000 : Int)
    geometryRow063_physicalVolume_numerator_no_slash geometryRow063_physicalVolume_numerator_parse
    geometryRow063_physicalVolume_denominator_parse geometryRow063_physicalVolume_denominator_nonzero

theorem geometryRow063_physicalVolume_read :
    rationalField geometryRowsJson063 "physical_volume" = .ok geometryRowsTyped063.physicalVolume :=
  original_rationalField_of_string geometryRowsJson063 "physical_volume" geometryRow063_physicalVolumeText
    geometryRowsTyped063.physicalVolume geometryRow063_physicalVolume_field geometryRow063_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_physicalVolume_complete"
  err.flush

noncomputable def geometryRow063_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow063_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow063_meanGapText : String := String.ofList (geometryRow063_meanGapNumeratorChars ++ '/' :: geometryRow063_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_meanGap_before_field"
  err.flush

theorem geometryRow063_meanGap_field :
    geometryRowsJson063.getObjVal? "mean_gap" = .ok (.str geometryRow063_meanGapText) := by rfl

theorem geometryRow063_meanGap_numerator_no_slash :
    geometryRow063_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow063_meanGap_numerator_parse :
    SourceJson.intChars geometryRow063_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow063_meanGap_denominator_parse :
    SourceJson.intChars geometryRow063_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow063_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow063_meanGap_parse :
    parseRational geometryRow063_meanGapText = .ok geometryRowsTyped063.meanGap :=
  original_rational_fraction_of_chars geometryRow063_meanGapNumeratorChars geometryRow063_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow063_meanGap_numerator_no_slash geometryRow063_meanGap_numerator_parse
    geometryRow063_meanGap_denominator_parse geometryRow063_meanGap_denominator_nonzero

theorem geometryRow063_meanGap_read :
    rationalField geometryRowsJson063 "mean_gap" = .ok geometryRowsTyped063.meanGap :=
  original_rationalField_of_string geometryRowsJson063 "mean_gap" geometryRow063_meanGapText
    geometryRowsTyped063.meanGap geometryRow063_meanGap_field geometryRow063_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_meanGap_complete"
  err.flush

noncomputable def geometryRow063_jensenBoundNumeratorChars : List Char := ['2', '4', '1', '3', '3', '9', '6', '1', '8', '7', '4', '6', '2', '6', '3', '0', '8', '1', '8', '5', '8', '0', '9', '1', '0', '1', '2', '5', '2', '7', '5', '5', '8', '8', '3', '8', '2', '3', '6', '5', '6', '9', '5', '9', '2', '4', '1', '7', '3', '0', '7', '9', '5', '8', '8', '2', '0', '1', '0', '1', '9', '7', '6', '7', '1', '6', '1', '2', '1', '1', '0', '2', '7', '7', '4', '3', '4', '8', '0', '9', '5', '6', '5', '6', '8', '2', '1', '5', '0', '6', '6', '1', '9', '9', '0', '7', '7', '3', '0', '2', '1', '3', '3', '1', '2', '8', '8', '7', '7', '3', '6', '6', '6', '1', '8', '8', '5', '3', '2', '9', '3', '3', '2', '2', '1', '5', '9', '2', '2', '8', '0', '3', '9', '0', '9', '7', '4', '6', '4', '7', '4', '7', '2', '3', '5', '4', '9', '6', '9', '2', '8', '8', '0', '5', '4', '9', '9', '8', '9', '1', '3', '3', '5', '1', '1', '9', '6', '7', '7', '7', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow063_jensenBoundDenominatorChars : List Char := ['5', '4', '7', '3', '3', '4', '5', '3', '3', '5', '0', '9', '4', '2', '9', '3', '8', '0', '7', '6', '7', '2', '9', '0', '8', '0', '5', '6', '6', '3', '0', '7', '3', '8', '3', '7', '0', '4', '6', '9', '3', '8', '5', '9', '5', '6', '0', '5', '0', '5', '7', '9', '9', '5', '8', '4', '0', '3', '5', '0', '5', '9', '3', '3', '8', '7', '8', '5', '5', '4', '2', '6', '4', '6', '0', '2', '7', '8', '6', '3', '1', '5', '2', '7', '2', '8', '2', '8', '5', '1', '8', '8', '5', '6', '2', '8', '4', '7', '4', '9', '7', '3', '4', '9', '0', '1', '8', '3', '1', '3', '4', '4', '8', '2', '6', '5', '0', '6', '4', '3', '7', '9', '7', '3', '0', '4', '0', '2', '2', '3', '2', '5', '2', '1', '2', '8', '9', '3', '6', '3', '6', '2', '2', '0', '5', '1', '0', '3', '9', '4', '7', '5', '3', '6', '8', '2', '6', '3', '1', '5', '7', '5', '3', '4', '0', '1', '0', '0', '9', '4', '8', '0', '7', '3', '5', '5', '6', '4', '2', '3', '6', '7', '1', '0', '8', '6', '6', '1', '8', '1', '3', '1', '8', '0', '7', '5', '0', '0', '4', '4', '5', '3', '1', '3']
noncomputable def geometryRow063_jensenBoundText : String := String.ofList (geometryRow063_jensenBoundNumeratorChars ++ '/' :: geometryRow063_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_jensenBound_before_field"
  err.flush

theorem geometryRow063_jensenBound_field :
    geometryRowsJson063.getObjVal? "jensen_bound" = .ok (.str geometryRow063_jensenBoundText) := by rfl

theorem geometryRow063_jensenBound_numerator_no_slash :
    geometryRow063_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow063_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow063_jensenBoundNumeratorChars = some (24133961874626308185809101252755883823656959241730795882010197671612110277434809565682150661990773021331288773666188532933221592280390974647472354969288054998913351196777343750000000000000 : Int) := by decide +kernel

theorem geometryRow063_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow063_jensenBoundDenominatorChars = some (547334533509429380767290805663073837046938595605057995840350593387855426460278631527282851885628474973490183134482650643797304022325212893636220510394753682631575340100948073556423671086618131807500445313 : Int) := by decide +kernel

theorem geometryRow063_jensenBound_denominator_nonzero : (547334533509429380767290805663073837046938595605057995840350593387855426460278631527282851885628474973490183134482650643797304022325212893636220510394753682631575340100948073556423671086618131807500445313 : Int) ≠ 0 := by decide +kernel

theorem geometryRow063_jensenBound_parse :
    parseRational geometryRow063_jensenBoundText = .ok geometryRowsTyped063.jensenBound :=
  original_rational_fraction_of_chars geometryRow063_jensenBoundNumeratorChars geometryRow063_jensenBoundDenominatorChars
    (24133961874626308185809101252755883823656959241730795882010197671612110277434809565682150661990773021331288773666188532933221592280390974647472354969288054998913351196777343750000000000000 : Int) (547334533509429380767290805663073837046938595605057995840350593387855426460278631527282851885628474973490183134482650643797304022325212893636220510394753682631575340100948073556423671086618131807500445313 : Int)
    geometryRow063_jensenBound_numerator_no_slash geometryRow063_jensenBound_numerator_parse
    geometryRow063_jensenBound_denominator_parse geometryRow063_jensenBound_denominator_nonzero

theorem geometryRow063_jensenBound_read :
    rationalField geometryRowsJson063 "jensen_bound" = .ok geometryRowsTyped063.jensenBound :=
  original_rationalField_of_string geometryRowsJson063 "jensen_bound" geometryRow063_jensenBoundText
    geometryRowsTyped063.jensenBound geometryRow063_jensenBound_field geometryRow063_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_factorMaxima_before"
  err.flush

theorem geometryRow063_factorMaxima_read :
    rationalArrayField geometryRowsJson063 "factor_maxima" = .ok geometryRowsTyped063.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_gapWeightedMeans_before"
  err.flush

theorem geometryRow063_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson063 "gap_weighted_means" = .ok geometryRowsTyped063.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow063_floorChars : List Char := ['3', '4', '9', '3', '4', '5', '6', '6', '2', '7', '4', '4', '1']
noncomputable def geometryRow063_floorText : String := String.ofList geometryRow063_floorChars

theorem geometryRow063_floor_text_read :
    geometryRowsJson063.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow063_floorText := by rfl

theorem geometryRow063_floor_chars_parse :
    SourceJson.intChars geometryRow063_floorChars = some (3493456627441 : Int) := by decide +kernel

theorem geometryRow063_floor_parse :
    parseInteger geometryRow063_floorText = .ok geometryRowsTyped063.jensenFloorQ96 := by
  simp only [geometryRow063_floorText, parseInteger, String.toList_ofList, geometryRow063_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_063 :
    decodeGeometryRow geometryRowsJson063 = .ok geometryRowsTyped063 :=
  original_geometryRow_of_fields geometryRowsJson063 geometryRowsTyped063 geometryRow063_floorText
    geometryRow063_simplexId_read geometryRow063_vertexIds_read
    geometryRow063_physicalVolume_read geometryRow063_meanGap_read
    geometryRow063_factorMaxima_read geometryRow063_gapWeightedMeans_read
    geometryRow063_jensenBound_read geometryRow063_floor_text_read geometryRow063_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_063_original_decoder_complete"
  err.flush

theorem geometryRow063_shape :
    geometryRowsTyped063.simplexId = 63 ∧
    geometryRowsTyped063.vertexIds.size = 9 ∧ geometryRowsTyped063.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped063.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped063.factorMaxima.size = 10 ∧ geometryRowsTyped063.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock007 : List SourceJson := [geometryRowsJson056, geometryRowsJson057, geometryRowsJson058, geometryRowsJson059, geometryRowsJson060, geometryRowsJson061, geometryRowsJson062, geometryRowsJson063]
noncomputable def geometryRowsTypedBlock007 : List GeometryRow := [geometryRowsTyped056, geometryRowsTyped057, geometryRowsTyped058, geometryRowsTyped059, geometryRowsTyped060, geometryRowsTyped061, geometryRowsTyped062, geometryRowsTyped063]

theorem geometry_Rows_block_007_push_eq (acc : List SourceJson) :
    SimplicesBlock007.blockPush acc = [geometryRowsJson063, geometryRowsJson062, geometryRowsJson061, geometryRowsJson060, geometryRowsJson059, geometryRowsJson058, geometryRowsJson057, geometryRowsJson056] ++ acc := by rfl

theorem geometry_Rows_block_007_reverse (acc : List SourceJson) :
    (SimplicesBlock007.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock007 := by
  rw [geometry_Rows_block_007_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_007 :
    geometryRowsJsonBlock007.mapM decodeGeometryRow = .ok geometryRowsTypedBlock007 := by
  simp only [geometryRowsJsonBlock007, geometryRowsTypedBlock007, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_056, decode_geometry_Rows_057, decode_geometry_Rows_058, decode_geometry_Rows_059, decode_geometry_Rows_060, decode_geometry_Rows_061, decode_geometry_Rows_062, decode_geometry_Rows_063]
  rfl

theorem geometry_Rows_block_007_length : geometryRowsTypedBlock007.length = 8 := by rfl

#print axioms geometryRow056_simplexId_read
#print axioms geometryRow056_vertexIds_read
#print axioms geometryRow056_physicalVolume_field
#print axioms geometryRow056_physicalVolume_numerator_no_slash
#print axioms geometryRow056_physicalVolume_numerator_parse
#print axioms geometryRow056_physicalVolume_denominator_parse
#print axioms geometryRow056_physicalVolume_denominator_nonzero
#print axioms geometryRow056_physicalVolume_parse
#print axioms geometryRow056_physicalVolume_read
#print axioms geometryRow056_meanGap_field
#print axioms geometryRow056_meanGap_numerator_no_slash
#print axioms geometryRow056_meanGap_numerator_parse
#print axioms geometryRow056_meanGap_denominator_parse
#print axioms geometryRow056_meanGap_denominator_nonzero
#print axioms geometryRow056_meanGap_parse
#print axioms geometryRow056_meanGap_read
#print axioms geometryRow056_jensenBound_field
#print axioms geometryRow056_jensenBound_numerator_no_slash
#print axioms geometryRow056_jensenBound_numerator_parse
#print axioms geometryRow056_jensenBound_denominator_parse
#print axioms geometryRow056_jensenBound_denominator_nonzero
#print axioms geometryRow056_jensenBound_parse
#print axioms geometryRow056_jensenBound_read
#print axioms geometryRow056_factorMaxima_read
#print axioms geometryRow056_gapWeightedMeans_read
#print axioms geometryRow056_floor_text_read
#print axioms geometryRow056_floor_chars_parse
#print axioms geometryRow056_floor_parse
#print axioms decode_geometry_Rows_056
#print axioms geometryRow056_shape
#print axioms geometryRow057_simplexId_read
#print axioms geometryRow057_vertexIds_read
#print axioms geometryRow057_physicalVolume_field
#print axioms geometryRow057_physicalVolume_numerator_no_slash
#print axioms geometryRow057_physicalVolume_numerator_parse
#print axioms geometryRow057_physicalVolume_denominator_parse
#print axioms geometryRow057_physicalVolume_denominator_nonzero
#print axioms geometryRow057_physicalVolume_parse
#print axioms geometryRow057_physicalVolume_read
#print axioms geometryRow057_meanGap_field
#print axioms geometryRow057_meanGap_numerator_no_slash
#print axioms geometryRow057_meanGap_numerator_parse
#print axioms geometryRow057_meanGap_denominator_parse
#print axioms geometryRow057_meanGap_denominator_nonzero
#print axioms geometryRow057_meanGap_parse
#print axioms geometryRow057_meanGap_read
#print axioms geometryRow057_jensenBound_field
#print axioms geometryRow057_jensenBound_numerator_no_slash
#print axioms geometryRow057_jensenBound_numerator_parse
#print axioms geometryRow057_jensenBound_denominator_parse
#print axioms geometryRow057_jensenBound_denominator_nonzero
#print axioms geometryRow057_jensenBound_parse
#print axioms geometryRow057_jensenBound_read
#print axioms geometryRow057_factorMaxima_read
#print axioms geometryRow057_gapWeightedMeans_read
#print axioms geometryRow057_floor_text_read
#print axioms geometryRow057_floor_chars_parse
#print axioms geometryRow057_floor_parse
#print axioms decode_geometry_Rows_057
#print axioms geometryRow057_shape
#print axioms geometryRow058_simplexId_read
#print axioms geometryRow058_vertexIds_read
#print axioms geometryRow058_physicalVolume_field
#print axioms geometryRow058_physicalVolume_numerator_no_slash
#print axioms geometryRow058_physicalVolume_numerator_parse
#print axioms geometryRow058_physicalVolume_denominator_parse
#print axioms geometryRow058_physicalVolume_denominator_nonzero
#print axioms geometryRow058_physicalVolume_parse
#print axioms geometryRow058_physicalVolume_read
#print axioms geometryRow058_meanGap_field
#print axioms geometryRow058_meanGap_numerator_no_slash
#print axioms geometryRow058_meanGap_numerator_parse
#print axioms geometryRow058_meanGap_denominator_parse
#print axioms geometryRow058_meanGap_denominator_nonzero
#print axioms geometryRow058_meanGap_parse
#print axioms geometryRow058_meanGap_read
#print axioms geometryRow058_jensenBound_field
#print axioms geometryRow058_jensenBound_numerator_no_slash
#print axioms geometryRow058_jensenBound_numerator_parse
#print axioms geometryRow058_jensenBound_denominator_parse
#print axioms geometryRow058_jensenBound_denominator_nonzero
#print axioms geometryRow058_jensenBound_parse
#print axioms geometryRow058_jensenBound_read
#print axioms geometryRow058_factorMaxima_read
#print axioms geometryRow058_gapWeightedMeans_read
#print axioms geometryRow058_floor_text_read
#print axioms geometryRow058_floor_chars_parse
#print axioms geometryRow058_floor_parse
#print axioms decode_geometry_Rows_058
#print axioms geometryRow058_shape
#print axioms geometryRow059_simplexId_read
#print axioms geometryRow059_vertexIds_read
#print axioms geometryRow059_physicalVolume_field
#print axioms geometryRow059_physicalVolume_numerator_no_slash
#print axioms geometryRow059_physicalVolume_numerator_parse
#print axioms geometryRow059_physicalVolume_denominator_parse
#print axioms geometryRow059_physicalVolume_denominator_nonzero
#print axioms geometryRow059_physicalVolume_parse
#print axioms geometryRow059_physicalVolume_read
#print axioms geometryRow059_meanGap_field
#print axioms geometryRow059_meanGap_numerator_no_slash
#print axioms geometryRow059_meanGap_numerator_parse
#print axioms geometryRow059_meanGap_denominator_parse
#print axioms geometryRow059_meanGap_denominator_nonzero
#print axioms geometryRow059_meanGap_parse
#print axioms geometryRow059_meanGap_read
#print axioms geometryRow059_jensenBound_field
#print axioms geometryRow059_jensenBound_numerator_no_slash
#print axioms geometryRow059_jensenBound_numerator_parse
#print axioms geometryRow059_jensenBound_denominator_parse
#print axioms geometryRow059_jensenBound_denominator_nonzero
#print axioms geometryRow059_jensenBound_parse
#print axioms geometryRow059_jensenBound_read
#print axioms geometryRow059_factorMaxima_read
#print axioms geometryRow059_gapWeightedMeans_read
#print axioms geometryRow059_floor_text_read
#print axioms geometryRow059_floor_chars_parse
#print axioms geometryRow059_floor_parse
#print axioms decode_geometry_Rows_059
#print axioms geometryRow059_shape
#print axioms geometryRow060_simplexId_read
#print axioms geometryRow060_vertexIds_read
#print axioms geometryRow060_physicalVolume_field
#print axioms geometryRow060_physicalVolume_numerator_no_slash
#print axioms geometryRow060_physicalVolume_numerator_parse
#print axioms geometryRow060_physicalVolume_denominator_parse
#print axioms geometryRow060_physicalVolume_denominator_nonzero
#print axioms geometryRow060_physicalVolume_parse
#print axioms geometryRow060_physicalVolume_read
#print axioms geometryRow060_meanGap_field
#print axioms geometryRow060_meanGap_numerator_no_slash
#print axioms geometryRow060_meanGap_numerator_parse
#print axioms geometryRow060_meanGap_denominator_parse
#print axioms geometryRow060_meanGap_denominator_nonzero
#print axioms geometryRow060_meanGap_parse
#print axioms geometryRow060_meanGap_read
#print axioms geometryRow060_jensenBound_field
#print axioms geometryRow060_jensenBound_numerator_no_slash
#print axioms geometryRow060_jensenBound_numerator_parse
#print axioms geometryRow060_jensenBound_denominator_parse
#print axioms geometryRow060_jensenBound_denominator_nonzero
#print axioms geometryRow060_jensenBound_parse
#print axioms geometryRow060_jensenBound_read
#print axioms geometryRow060_factorMaxima_read
#print axioms geometryRow060_gapWeightedMeans_read
#print axioms geometryRow060_floor_text_read
#print axioms geometryRow060_floor_chars_parse
#print axioms geometryRow060_floor_parse
#print axioms decode_geometry_Rows_060
#print axioms geometryRow060_shape
#print axioms geometryRow061_simplexId_read
#print axioms geometryRow061_vertexIds_read
#print axioms geometryRow061_physicalVolume_field
#print axioms geometryRow061_physicalVolume_numerator_no_slash
#print axioms geometryRow061_physicalVolume_numerator_parse
#print axioms geometryRow061_physicalVolume_denominator_parse
#print axioms geometryRow061_physicalVolume_denominator_nonzero
#print axioms geometryRow061_physicalVolume_parse
#print axioms geometryRow061_physicalVolume_read
#print axioms geometryRow061_meanGap_field
#print axioms geometryRow061_meanGap_numerator_no_slash
#print axioms geometryRow061_meanGap_numerator_parse
#print axioms geometryRow061_meanGap_denominator_parse
#print axioms geometryRow061_meanGap_denominator_nonzero
#print axioms geometryRow061_meanGap_parse
#print axioms geometryRow061_meanGap_read
#print axioms geometryRow061_jensenBound_field
#print axioms geometryRow061_jensenBound_numerator_no_slash
#print axioms geometryRow061_jensenBound_numerator_parse
#print axioms geometryRow061_jensenBound_denominator_parse
#print axioms geometryRow061_jensenBound_denominator_nonzero
#print axioms geometryRow061_jensenBound_parse
#print axioms geometryRow061_jensenBound_read
#print axioms geometryRow061_factorMaxima_read
#print axioms geometryRow061_gapWeightedMeans_read
#print axioms geometryRow061_floor_text_read
#print axioms geometryRow061_floor_chars_parse
#print axioms geometryRow061_floor_parse
#print axioms decode_geometry_Rows_061
#print axioms geometryRow061_shape
#print axioms geometryRow062_simplexId_read
#print axioms geometryRow062_vertexIds_read
#print axioms geometryRow062_physicalVolume_field
#print axioms geometryRow062_physicalVolume_numerator_no_slash
#print axioms geometryRow062_physicalVolume_numerator_parse
#print axioms geometryRow062_physicalVolume_denominator_parse
#print axioms geometryRow062_physicalVolume_denominator_nonzero
#print axioms geometryRow062_physicalVolume_parse
#print axioms geometryRow062_physicalVolume_read
#print axioms geometryRow062_meanGap_field
#print axioms geometryRow062_meanGap_numerator_no_slash
#print axioms geometryRow062_meanGap_numerator_parse
#print axioms geometryRow062_meanGap_denominator_parse
#print axioms geometryRow062_meanGap_denominator_nonzero
#print axioms geometryRow062_meanGap_parse
#print axioms geometryRow062_meanGap_read
#print axioms geometryRow062_jensenBound_field
#print axioms geometryRow062_jensenBound_numerator_no_slash
#print axioms geometryRow062_jensenBound_numerator_parse
#print axioms geometryRow062_jensenBound_denominator_parse
#print axioms geometryRow062_jensenBound_denominator_nonzero
#print axioms geometryRow062_jensenBound_parse
#print axioms geometryRow062_jensenBound_read
#print axioms geometryRow062_factorMaxima_read
#print axioms geometryRow062_gapWeightedMeans_read
#print axioms geometryRow062_floor_text_read
#print axioms geometryRow062_floor_chars_parse
#print axioms geometryRow062_floor_parse
#print axioms decode_geometry_Rows_062
#print axioms geometryRow062_shape
#print axioms geometryRow063_simplexId_read
#print axioms geometryRow063_vertexIds_read
#print axioms geometryRow063_physicalVolume_field
#print axioms geometryRow063_physicalVolume_numerator_no_slash
#print axioms geometryRow063_physicalVolume_numerator_parse
#print axioms geometryRow063_physicalVolume_denominator_parse
#print axioms geometryRow063_physicalVolume_denominator_nonzero
#print axioms geometryRow063_physicalVolume_parse
#print axioms geometryRow063_physicalVolume_read
#print axioms geometryRow063_meanGap_field
#print axioms geometryRow063_meanGap_numerator_no_slash
#print axioms geometryRow063_meanGap_numerator_parse
#print axioms geometryRow063_meanGap_denominator_parse
#print axioms geometryRow063_meanGap_denominator_nonzero
#print axioms geometryRow063_meanGap_parse
#print axioms geometryRow063_meanGap_read
#print axioms geometryRow063_jensenBound_field
#print axioms geometryRow063_jensenBound_numerator_no_slash
#print axioms geometryRow063_jensenBound_numerator_parse
#print axioms geometryRow063_jensenBound_denominator_parse
#print axioms geometryRow063_jensenBound_denominator_nonzero
#print axioms geometryRow063_jensenBound_parse
#print axioms geometryRow063_jensenBound_read
#print axioms geometryRow063_factorMaxima_read
#print axioms geometryRow063_gapWeightedMeans_read
#print axioms geometryRow063_floor_text_read
#print axioms geometryRow063_floor_chars_parse
#print axioms geometryRow063_floor_parse
#print axioms decode_geometry_Rows_063
#print axioms geometryRow063_shape
#print axioms geometry_Rows_block_007_push_eq
#print axioms geometry_Rows_block_007_reverse
#print axioms decode_geometry_Rows_block_007
#print axioms geometry_Rows_block_007_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
