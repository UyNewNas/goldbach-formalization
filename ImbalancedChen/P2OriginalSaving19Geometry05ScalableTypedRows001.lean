import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableSimplicesBlock001

/-! Local typed certificates for original cell 05, rows 8 through 15.
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

noncomputable def geometryRowsJson008 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped008 : GeometryRow :=
  { simplexId := 8,
    vertexIds := #[27, 25, 11, 9, 7, 5, 3, 2, 0],
    physicalVolume := ((5210898164784505428623549214177466243 : ℚ) / (221217681678336000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((38045395709 : ℚ) / (408318750000 : ℚ)), ((1223755201903 : ℚ) / (13066200000000 : ℚ)), ((619511787667 : ℚ) / (5226480000000 : ℚ)), ((2265034241203 : ℚ) / (26132400000000 : ℚ)), ((2176404957397 : ℚ) / (26132400000000 : ℚ)), ((394827446717 : ℚ) / (5226480000000 : ℚ)), ((126903339791 : ℚ) / (3266550000000 : ℚ)), ((149897634647 : ℚ) / (4355400000000 : ℚ)), ((48978208059 : ℚ) / (1451800000000 : ℚ)), ((107223389849 : ℚ) / (3266550000000 : ℚ))],
    jensenBound := ((42460631041704787466081225500702429768347806159693746587553833710539665914062500000000000000000 : ℚ) / (1404523437577055935638734146635008685287673426268650869337280981773847134757940128882791827726714375455838534177 : ℚ)),
    jensenFloorQ96 := (2395173826670 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_simplexId_before"
  err.flush

theorem geometryRow008_simplexId_read :
    geometryRowsJson008.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped008.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_vertexIds_before"
  err.flush

theorem geometryRow008_vertexIds_read :
    geometryRowsJson008.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped008.vertexIds := by decide +kernel

noncomputable def geometryRow008_physicalVolumeNumeratorChars : List Char := ['5', '2', '1', '0', '8', '9', '8', '1', '6', '4', '7', '8', '4', '5', '0', '5', '4', '2', '8', '6', '2', '3', '5', '4', '9', '2', '1', '4', '1', '7', '7', '4', '6', '6', '2', '4', '3']
noncomputable def geometryRow008_physicalVolumeDenominatorChars : List Char := ['2', '2', '1', '2', '1', '7', '6', '8', '1', '6', '7', '8', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow008_physicalVolumeText : String := String.ofList (geometryRow008_physicalVolumeNumeratorChars ++ '/' :: geometryRow008_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_physicalVolume_before_field"
  err.flush

theorem geometryRow008_physicalVolume_field :
    geometryRowsJson008.getObjVal? "physical_volume" = .ok (.str geometryRow008_physicalVolumeText) := by rfl

theorem geometryRow008_physicalVolume_numerator_no_slash :
    geometryRow008_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow008_physicalVolumeNumeratorChars = some (5210898164784505428623549214177466243 : Int) := by decide +kernel

theorem geometryRow008_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow008_physicalVolumeDenominatorChars = some (221217681678336000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow008_physicalVolume_denominator_nonzero : (221217681678336000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_physicalVolume_parse :
    parseRational geometryRow008_physicalVolumeText = .ok geometryRowsTyped008.physicalVolume :=
  original_rational_fraction_of_chars geometryRow008_physicalVolumeNumeratorChars geometryRow008_physicalVolumeDenominatorChars
    (5210898164784505428623549214177466243 : Int) (221217681678336000000000000000000000000000000000000000000000000 : Int)
    geometryRow008_physicalVolume_numerator_no_slash geometryRow008_physicalVolume_numerator_parse
    geometryRow008_physicalVolume_denominator_parse geometryRow008_physicalVolume_denominator_nonzero

theorem geometryRow008_physicalVolume_read :
    rationalField geometryRowsJson008 "physical_volume" = .ok geometryRowsTyped008.physicalVolume :=
  original_rationalField_of_string geometryRowsJson008 "physical_volume" geometryRow008_physicalVolumeText
    geometryRowsTyped008.physicalVolume geometryRow008_physicalVolume_field geometryRow008_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_physicalVolume_complete"
  err.flush

noncomputable def geometryRow008_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow008_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow008_meanGapText : String := String.ofList (geometryRow008_meanGapNumeratorChars ++ '/' :: geometryRow008_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_meanGap_before_field"
  err.flush

theorem geometryRow008_meanGap_field :
    geometryRowsJson008.getObjVal? "mean_gap" = .ok (.str geometryRow008_meanGapText) := by rfl

theorem geometryRow008_meanGap_numerator_no_slash :
    geometryRow008_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_meanGap_numerator_parse :
    SourceJson.intChars geometryRow008_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow008_meanGap_denominator_parse :
    SourceJson.intChars geometryRow008_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow008_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_meanGap_parse :
    parseRational geometryRow008_meanGapText = .ok geometryRowsTyped008.meanGap :=
  original_rational_fraction_of_chars geometryRow008_meanGapNumeratorChars geometryRow008_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow008_meanGap_numerator_no_slash geometryRow008_meanGap_numerator_parse
    geometryRow008_meanGap_denominator_parse geometryRow008_meanGap_denominator_nonzero

theorem geometryRow008_meanGap_read :
    rationalField geometryRowsJson008 "mean_gap" = .ok geometryRowsTyped008.meanGap :=
  original_rationalField_of_string geometryRowsJson008 "mean_gap" geometryRow008_meanGapText
    geometryRowsTyped008.meanGap geometryRow008_meanGap_field geometryRow008_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_meanGap_complete"
  err.flush

noncomputable def geometryRow008_jensenBoundNumeratorChars : List Char := ['4', '2', '4', '6', '0', '6', '3', '1', '0', '4', '1', '7', '0', '4', '7', '8', '7', '4', '6', '6', '0', '8', '1', '2', '2', '5', '5', '0', '0', '7', '0', '2', '4', '2', '9', '7', '6', '8', '3', '4', '7', '8', '0', '6', '1', '5', '9', '6', '9', '3', '7', '4', '6', '5', '8', '7', '5', '5', '3', '8', '3', '3', '7', '1', '0', '5', '3', '9', '6', '6', '5', '9', '1', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow008_jensenBoundDenominatorChars : List Char := ['1', '4', '0', '4', '5', '2', '3', '4', '3', '7', '5', '7', '7', '0', '5', '5', '9', '3', '5', '6', '3', '8', '7', '3', '4', '1', '4', '6', '6', '3', '5', '0', '0', '8', '6', '8', '5', '2', '8', '7', '6', '7', '3', '4', '2', '6', '2', '6', '8', '6', '5', '0', '8', '6', '9', '3', '3', '7', '2', '8', '0', '9', '8', '1', '7', '7', '3', '8', '4', '7', '1', '3', '4', '7', '5', '7', '9', '4', '0', '1', '2', '8', '8', '8', '2', '7', '9', '1', '8', '2', '7', '7', '2', '6', '7', '1', '4', '3', '7', '5', '4', '5', '5', '8', '3', '8', '5', '3', '4', '1', '7', '7']
noncomputable def geometryRow008_jensenBoundText : String := String.ofList (geometryRow008_jensenBoundNumeratorChars ++ '/' :: geometryRow008_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_jensenBound_before_field"
  err.flush

theorem geometryRow008_jensenBound_field :
    geometryRowsJson008.getObjVal? "jensen_bound" = .ok (.str geometryRow008_jensenBoundText) := by rfl

theorem geometryRow008_jensenBound_numerator_no_slash :
    geometryRow008_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow008_jensenBoundNumeratorChars = some (42460631041704787466081225500702429768347806159693746587553833710539665914062500000000000000000 : Int) := by decide +kernel

theorem geometryRow008_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow008_jensenBoundDenominatorChars = some (1404523437577055935638734146635008685287673426268650869337280981773847134757940128882791827726714375455838534177 : Int) := by decide +kernel

theorem geometryRow008_jensenBound_denominator_nonzero : (1404523437577055935638734146635008685287673426268650869337280981773847134757940128882791827726714375455838534177 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_jensenBound_parse :
    parseRational geometryRow008_jensenBoundText = .ok geometryRowsTyped008.jensenBound :=
  original_rational_fraction_of_chars geometryRow008_jensenBoundNumeratorChars geometryRow008_jensenBoundDenominatorChars
    (42460631041704787466081225500702429768347806159693746587553833710539665914062500000000000000000 : Int) (1404523437577055935638734146635008685287673426268650869337280981773847134757940128882791827726714375455838534177 : Int)
    geometryRow008_jensenBound_numerator_no_slash geometryRow008_jensenBound_numerator_parse
    geometryRow008_jensenBound_denominator_parse geometryRow008_jensenBound_denominator_nonzero

theorem geometryRow008_jensenBound_read :
    rationalField geometryRowsJson008 "jensen_bound" = .ok geometryRowsTyped008.jensenBound :=
  original_rationalField_of_string geometryRowsJson008 "jensen_bound" geometryRow008_jensenBoundText
    geometryRowsTyped008.jensenBound geometryRow008_jensenBound_field geometryRow008_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_factorMaxima_before"
  err.flush

theorem geometryRow008_factorMaxima_read :
    rationalArrayField geometryRowsJson008 "factor_maxima" = .ok geometryRowsTyped008.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_gapWeightedMeans_before"
  err.flush

theorem geometryRow008_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson008 "gap_weighted_means" = .ok geometryRowsTyped008.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow008_floorChars : List Char := ['2', '3', '9', '5', '1', '7', '3', '8', '2', '6', '6', '7', '0']
noncomputable def geometryRow008_floorText : String := String.ofList geometryRow008_floorChars

theorem geometryRow008_floor_text_read :
    geometryRowsJson008.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow008_floorText := by rfl

theorem geometryRow008_floor_chars_parse :
    SourceJson.intChars geometryRow008_floorChars = some (2395173826670 : Int) := by decide +kernel

theorem geometryRow008_floor_parse :
    parseInteger geometryRow008_floorText = .ok geometryRowsTyped008.jensenFloorQ96 := by
  simp only [geometryRow008_floorText, parseInteger, String.toList_ofList, geometryRow008_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_008 :
    decodeGeometryRow geometryRowsJson008 = .ok geometryRowsTyped008 :=
  original_geometryRow_of_fields geometryRowsJson008 geometryRowsTyped008 geometryRow008_floorText
    geometryRow008_simplexId_read geometryRow008_vertexIds_read
    geometryRow008_physicalVolume_read geometryRow008_meanGap_read
    geometryRow008_factorMaxima_read geometryRow008_gapWeightedMeans_read
    geometryRow008_jensenBound_read geometryRow008_floor_text_read geometryRow008_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_008_original_decoder_complete"
  err.flush

theorem geometryRow008_shape :
    geometryRowsTyped008.simplexId = 8 ∧
    geometryRowsTyped008.vertexIds.size = 9 ∧ geometryRowsTyped008.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped008.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped008.factorMaxima.size = 10 ∧ geometryRowsTyped008.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson009 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped009 : GeometryRow :=
  { simplexId := 9,
    vertexIds := #[27, 25, 11, 9, 7, 5, 4, 2, 0],
    physicalVolume := ((569976731856029777966425952640056219209873 : ℚ) / (9438621084942336000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((10824169 : ℚ) / (19584000000 : ℚ)),
    factorMaxima := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((208562091217152597457 : ℚ) / (2262892111804800000000 : ℚ)), ((6570345889769626211 : ℚ) / (70715378493900000000 : ℚ)), ((1788967613920135567 : ℚ) / (15085947412032000000 : ℚ)), ((8250471428354543449 : ℚ) / (94287171325200000000 : ℚ)), ((327679474788873729 : ℚ) / (3928632138550000000 : ℚ)), ((1413625893667525441 : ℚ) / (18857434265040000000 : ℚ)), ((14890178050673635931 : ℚ) / (377148685300800000000 : ℚ)), ((38858392768896971717 : ℚ) / (1131446055902400000000 : ℚ)), ((38182493158881927197 : ℚ) / (1131446055902400000000 : ℚ)), ((511918806268651281 : ℚ) / (15714528554200000000 : ℚ))],
    jensenBound := ((51242643757441138119871051662988280970407425984678805711967787099523666159880912654121278915131968856546822168151134832030193916551014102230420959413917600000000000000000000000 : ℚ) / (317877600430492127938398122726265677822948895817497919283883916978870928774779245005173555731646910055993311989316448260487738849315298641702957334097081011375946118816428871879776393048133 : ℚ)),
    jensenFloorQ96 := (12771772851490484 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_simplexId_before"
  err.flush

theorem geometryRow009_simplexId_read :
    geometryRowsJson009.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped009.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_vertexIds_before"
  err.flush

theorem geometryRow009_vertexIds_read :
    geometryRowsJson009.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped009.vertexIds := by decide +kernel

noncomputable def geometryRow009_physicalVolumeNumeratorChars : List Char := ['5', '6', '9', '9', '7', '6', '7', '3', '1', '8', '5', '6', '0', '2', '9', '7', '7', '7', '9', '6', '6', '4', '2', '5', '9', '5', '2', '6', '4', '0', '0', '5', '6', '2', '1', '9', '2', '0', '9', '8', '7', '3']
noncomputable def geometryRow009_physicalVolumeDenominatorChars : List Char := ['9', '4', '3', '8', '6', '2', '1', '0', '8', '4', '9', '4', '2', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_physicalVolumeText : String := String.ofList (geometryRow009_physicalVolumeNumeratorChars ++ '/' :: geometryRow009_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_physicalVolume_before_field"
  err.flush

theorem geometryRow009_physicalVolume_field :
    geometryRowsJson009.getObjVal? "physical_volume" = .ok (.str geometryRow009_physicalVolumeText) := by rfl

theorem geometryRow009_physicalVolume_numerator_no_slash :
    geometryRow009_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow009_physicalVolumeNumeratorChars = some (569976731856029777966425952640056219209873 : Int) := by decide +kernel

theorem geometryRow009_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow009_physicalVolumeDenominatorChars = some (9438621084942336000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow009_physicalVolume_denominator_nonzero : (9438621084942336000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_physicalVolume_parse :
    parseRational geometryRow009_physicalVolumeText = .ok geometryRowsTyped009.physicalVolume :=
  original_rational_fraction_of_chars geometryRow009_physicalVolumeNumeratorChars geometryRow009_physicalVolumeDenominatorChars
    (569976731856029777966425952640056219209873 : Int) (9438621084942336000000000000000000000000000000000000000000000000 : Int)
    geometryRow009_physicalVolume_numerator_no_slash geometryRow009_physicalVolume_numerator_parse
    geometryRow009_physicalVolume_denominator_parse geometryRow009_physicalVolume_denominator_nonzero

theorem geometryRow009_physicalVolume_read :
    rationalField geometryRowsJson009 "physical_volume" = .ok geometryRowsTyped009.physicalVolume :=
  original_rationalField_of_string geometryRowsJson009 "physical_volume" geometryRow009_physicalVolumeText
    geometryRowsTyped009.physicalVolume geometryRow009_physicalVolume_field geometryRow009_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_physicalVolume_complete"
  err.flush

noncomputable def geometryRow009_meanGapNumeratorChars : List Char := ['1', '0', '8', '2', '4', '1', '6', '9']
noncomputable def geometryRow009_meanGapDenominatorChars : List Char := ['1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_meanGapText : String := String.ofList (geometryRow009_meanGapNumeratorChars ++ '/' :: geometryRow009_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_meanGap_before_field"
  err.flush

theorem geometryRow009_meanGap_field :
    geometryRowsJson009.getObjVal? "mean_gap" = .ok (.str geometryRow009_meanGapText) := by rfl

theorem geometryRow009_meanGap_numerator_no_slash :
    geometryRow009_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_meanGap_numerator_parse :
    SourceJson.intChars geometryRow009_meanGapNumeratorChars = some (10824169 : Int) := by decide +kernel

theorem geometryRow009_meanGap_denominator_parse :
    SourceJson.intChars geometryRow009_meanGapDenominatorChars = some (19584000000 : Int) := by decide +kernel

theorem geometryRow009_meanGap_denominator_nonzero : (19584000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_meanGap_parse :
    parseRational geometryRow009_meanGapText = .ok geometryRowsTyped009.meanGap :=
  original_rational_fraction_of_chars geometryRow009_meanGapNumeratorChars geometryRow009_meanGapDenominatorChars
    (10824169 : Int) (19584000000 : Int)
    geometryRow009_meanGap_numerator_no_slash geometryRow009_meanGap_numerator_parse
    geometryRow009_meanGap_denominator_parse geometryRow009_meanGap_denominator_nonzero

theorem geometryRow009_meanGap_read :
    rationalField geometryRowsJson009 "mean_gap" = .ok geometryRowsTyped009.meanGap :=
  original_rationalField_of_string geometryRowsJson009 "mean_gap" geometryRow009_meanGapText
    geometryRowsTyped009.meanGap geometryRow009_meanGap_field geometryRow009_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_meanGap_complete"
  err.flush

noncomputable def geometryRow009_jensenBoundNumeratorChars : List Char := ['5', '1', '2', '4', '2', '6', '4', '3', '7', '5', '7', '4', '4', '1', '1', '3', '8', '1', '1', '9', '8', '7', '1', '0', '5', '1', '6', '6', '2', '9', '8', '8', '2', '8', '0', '9', '7', '0', '4', '0', '7', '4', '2', '5', '9', '8', '4', '6', '7', '8', '8', '0', '5', '7', '1', '1', '9', '6', '7', '7', '8', '7', '0', '9', '9', '5', '2', '3', '6', '6', '6', '1', '5', '9', '8', '8', '0', '9', '1', '2', '6', '5', '4', '1', '2', '1', '2', '7', '8', '9', '1', '5', '1', '3', '1', '9', '6', '8', '8', '5', '6', '5', '4', '6', '8', '2', '2', '1', '6', '8', '1', '5', '1', '1', '3', '4', '8', '3', '2', '0', '3', '0', '1', '9', '3', '9', '1', '6', '5', '5', '1', '0', '1', '4', '1', '0', '2', '2', '3', '0', '4', '2', '0', '9', '5', '9', '4', '1', '3', '9', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_jensenBoundDenominatorChars : List Char := ['3', '1', '7', '8', '7', '7', '6', '0', '0', '4', '3', '0', '4', '9', '2', '1', '2', '7', '9', '3', '8', '3', '9', '8', '1', '2', '2', '7', '2', '6', '2', '6', '5', '6', '7', '7', '8', '2', '2', '9', '4', '8', '8', '9', '5', '8', '1', '7', '4', '9', '7', '9', '1', '9', '2', '8', '3', '8', '8', '3', '9', '1', '6', '9', '7', '8', '8', '7', '0', '9', '2', '8', '7', '7', '4', '7', '7', '9', '2', '4', '5', '0', '0', '5', '1', '7', '3', '5', '5', '5', '7', '3', '1', '6', '4', '6', '9', '1', '0', '0', '5', '5', '9', '9', '3', '3', '1', '1', '9', '8', '9', '3', '1', '6', '4', '4', '8', '2', '6', '0', '4', '8', '7', '7', '3', '8', '8', '4', '9', '3', '1', '5', '2', '9', '8', '6', '4', '1', '7', '0', '2', '9', '5', '7', '3', '3', '4', '0', '9', '7', '0', '8', '1', '0', '1', '1', '3', '7', '5', '9', '4', '6', '1', '1', '8', '8', '1', '6', '4', '2', '8', '8', '7', '1', '8', '7', '9', '7', '7', '6', '3', '9', '3', '0', '4', '8', '1', '3', '3']
noncomputable def geometryRow009_jensenBoundText : String := String.ofList (geometryRow009_jensenBoundNumeratorChars ++ '/' :: geometryRow009_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_jensenBound_before_field"
  err.flush

theorem geometryRow009_jensenBound_field :
    geometryRowsJson009.getObjVal? "jensen_bound" = .ok (.str geometryRow009_jensenBoundText) := by rfl

theorem geometryRow009_jensenBound_numerator_no_slash :
    geometryRow009_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow009_jensenBoundNumeratorChars = some (51242643757441138119871051662988280970407425984678805711967787099523666159880912654121278915131968856546822168151134832030193916551014102230420959413917600000000000000000000000 : Int) := by decide +kernel

theorem geometryRow009_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow009_jensenBoundDenominatorChars = some (317877600430492127938398122726265677822948895817497919283883916978870928774779245005173555731646910055993311989316448260487738849315298641702957334097081011375946118816428871879776393048133 : Int) := by decide +kernel

theorem geometryRow009_jensenBound_denominator_nonzero : (317877600430492127938398122726265677822948895817497919283883916978870928774779245005173555731646910055993311989316448260487738849315298641702957334097081011375946118816428871879776393048133 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_jensenBound_parse :
    parseRational geometryRow009_jensenBoundText = .ok geometryRowsTyped009.jensenBound :=
  original_rational_fraction_of_chars geometryRow009_jensenBoundNumeratorChars geometryRow009_jensenBoundDenominatorChars
    (51242643757441138119871051662988280970407425984678805711967787099523666159880912654121278915131968856546822168151134832030193916551014102230420959413917600000000000000000000000 : Int) (317877600430492127938398122726265677822948895817497919283883916978870928774779245005173555731646910055993311989316448260487738849315298641702957334097081011375946118816428871879776393048133 : Int)
    geometryRow009_jensenBound_numerator_no_slash geometryRow009_jensenBound_numerator_parse
    geometryRow009_jensenBound_denominator_parse geometryRow009_jensenBound_denominator_nonzero

theorem geometryRow009_jensenBound_read :
    rationalField geometryRowsJson009 "jensen_bound" = .ok geometryRowsTyped009.jensenBound :=
  original_rationalField_of_string geometryRowsJson009 "jensen_bound" geometryRow009_jensenBoundText
    geometryRowsTyped009.jensenBound geometryRow009_jensenBound_field geometryRow009_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_factorMaxima_before"
  err.flush

theorem geometryRow009_factorMaxima_read :
    rationalArrayField geometryRowsJson009 "factor_maxima" = .ok geometryRowsTyped009.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_gapWeightedMeans_before"
  err.flush

theorem geometryRow009_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson009 "gap_weighted_means" = .ok geometryRowsTyped009.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow009_floorChars : List Char := ['1', '2', '7', '7', '1', '7', '7', '2', '8', '5', '1', '4', '9', '0', '4', '8', '4']
noncomputable def geometryRow009_floorText : String := String.ofList geometryRow009_floorChars

theorem geometryRow009_floor_text_read :
    geometryRowsJson009.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow009_floorText := by rfl

theorem geometryRow009_floor_chars_parse :
    SourceJson.intChars geometryRow009_floorChars = some (12771772851490484 : Int) := by decide +kernel

theorem geometryRow009_floor_parse :
    parseInteger geometryRow009_floorText = .ok geometryRowsTyped009.jensenFloorQ96 := by
  simp only [geometryRow009_floorText, parseInteger, String.toList_ofList, geometryRow009_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_009 :
    decodeGeometryRow geometryRowsJson009 = .ok geometryRowsTyped009 :=
  original_geometryRow_of_fields geometryRowsJson009 geometryRowsTyped009 geometryRow009_floorText
    geometryRow009_simplexId_read geometryRow009_vertexIds_read
    geometryRow009_physicalVolume_read geometryRow009_meanGap_read
    geometryRow009_factorMaxima_read geometryRow009_gapWeightedMeans_read
    geometryRow009_jensenBound_read geometryRow009_floor_text_read geometryRow009_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_009_original_decoder_complete"
  err.flush

theorem geometryRow009_shape :
    geometryRowsTyped009.simplexId = 9 ∧
    geometryRowsTyped009.vertexIds.size = 9 ∧ geometryRowsTyped009.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped009.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped009.factorMaxima.size = 10 ∧ geometryRowsTyped009.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson010 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped010 : GeometryRow :=
  { simplexId := 10,
    vertexIds := #[27, 25, 11, 9, 7, 6, 4, 2, 0],
    physicalVolume := ((40704311062587374412429639554588134813913 : ℚ) / (262734725578752000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((60031443907597 : ℚ) / (651772800000000 : ℚ)), ((943210728643 : ℚ) / (10183950000000 : ℚ)), ((2577496345679 : ℚ) / (21725760000000 : ℚ)), ((2367756675709 : ℚ) / (27157200000000 : ℚ)), ((47130475177 : ℚ) / (565775000000 : ℚ)), ((407734818373 : ℚ) / (5431440000000 : ℚ)), ((4283033652671 : ℚ) / (108628800000000 : ℚ)), ((11243829560417 : ℚ) / (325886400000000 : ℚ)), ((11126986998497 : ℚ) / (325886400000000 : ℚ)), ((147000827431 : ℚ) / (4526200000000 : ℚ))],
    jensenBound := ((332644121498925507842224268834149130449387159614580303350578909864199469072583881190512000000000000000000000000 : ℚ) / (1569230072596164773284270345782121655422581967791903241424824213721801308919583005781543800265547794435726632186317593298347 : ℚ)),
    jensenFloorQ96 := (16794721805152316 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_simplexId_before"
  err.flush

theorem geometryRow010_simplexId_read :
    geometryRowsJson010.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped010.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_vertexIds_before"
  err.flush

theorem geometryRow010_vertexIds_read :
    geometryRowsJson010.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped010.vertexIds := by decide +kernel

noncomputable def geometryRow010_physicalVolumeNumeratorChars : List Char := ['4', '0', '7', '0', '4', '3', '1', '1', '0', '6', '2', '5', '8', '7', '3', '7', '4', '4', '1', '2', '4', '2', '9', '6', '3', '9', '5', '5', '4', '5', '8', '8', '1', '3', '4', '8', '1', '3', '9', '1', '3']
noncomputable def geometryRow010_physicalVolumeDenominatorChars : List Char := ['2', '6', '2', '7', '3', '4', '7', '2', '5', '5', '7', '8', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow010_physicalVolumeText : String := String.ofList (geometryRow010_physicalVolumeNumeratorChars ++ '/' :: geometryRow010_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_physicalVolume_before_field"
  err.flush

theorem geometryRow010_physicalVolume_field :
    geometryRowsJson010.getObjVal? "physical_volume" = .ok (.str geometryRow010_physicalVolumeText) := by rfl

theorem geometryRow010_physicalVolume_numerator_no_slash :
    geometryRow010_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow010_physicalVolumeNumeratorChars = some (40704311062587374412429639554588134813913 : Int) := by decide +kernel

theorem geometryRow010_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow010_physicalVolumeDenominatorChars = some (262734725578752000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow010_physicalVolume_denominator_nonzero : (262734725578752000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_physicalVolume_parse :
    parseRational geometryRow010_physicalVolumeText = .ok geometryRowsTyped010.physicalVolume :=
  original_rational_fraction_of_chars geometryRow010_physicalVolumeNumeratorChars geometryRow010_physicalVolumeDenominatorChars
    (40704311062587374412429639554588134813913 : Int) (262734725578752000000000000000000000000000000000000000000000000 : Int)
    geometryRow010_physicalVolume_numerator_no_slash geometryRow010_physicalVolume_numerator_parse
    geometryRow010_physicalVolume_denominator_parse geometryRow010_physicalVolume_denominator_nonzero

theorem geometryRow010_physicalVolume_read :
    rationalField geometryRowsJson010 "physical_volume" = .ok geometryRowsTyped010.physicalVolume :=
  original_rationalField_of_string geometryRowsJson010 "physical_volume" geometryRow010_physicalVolumeText
    geometryRowsTyped010.physicalVolume geometryRow010_physicalVolume_field geometryRow010_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_physicalVolume_complete"
  err.flush

noncomputable def geometryRow010_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow010_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow010_meanGapText : String := String.ofList (geometryRow010_meanGapNumeratorChars ++ '/' :: geometryRow010_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_meanGap_before_field"
  err.flush

theorem geometryRow010_meanGap_field :
    geometryRowsJson010.getObjVal? "mean_gap" = .ok (.str geometryRow010_meanGapText) := by rfl

theorem geometryRow010_meanGap_numerator_no_slash :
    geometryRow010_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_meanGap_numerator_parse :
    SourceJson.intChars geometryRow010_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow010_meanGap_denominator_parse :
    SourceJson.intChars geometryRow010_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow010_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_meanGap_parse :
    parseRational geometryRow010_meanGapText = .ok geometryRowsTyped010.meanGap :=
  original_rational_fraction_of_chars geometryRow010_meanGapNumeratorChars geometryRow010_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow010_meanGap_numerator_no_slash geometryRow010_meanGap_numerator_parse
    geometryRow010_meanGap_denominator_parse geometryRow010_meanGap_denominator_nonzero

theorem geometryRow010_meanGap_read :
    rationalField geometryRowsJson010 "mean_gap" = .ok geometryRowsTyped010.meanGap :=
  original_rationalField_of_string geometryRowsJson010 "mean_gap" geometryRow010_meanGapText
    geometryRowsTyped010.meanGap geometryRow010_meanGap_field geometryRow010_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_meanGap_complete"
  err.flush

noncomputable def geometryRow010_jensenBoundNumeratorChars : List Char := ['3', '3', '2', '6', '4', '4', '1', '2', '1', '4', '9', '8', '9', '2', '5', '5', '0', '7', '8', '4', '2', '2', '2', '4', '2', '6', '8', '8', '3', '4', '1', '4', '9', '1', '3', '0', '4', '4', '9', '3', '8', '7', '1', '5', '9', '6', '1', '4', '5', '8', '0', '3', '0', '3', '3', '5', '0', '5', '7', '8', '9', '0', '9', '8', '6', '4', '1', '9', '9', '4', '6', '9', '0', '7', '2', '5', '8', '3', '8', '8', '1', '1', '9', '0', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow010_jensenBoundDenominatorChars : List Char := ['1', '5', '6', '9', '2', '3', '0', '0', '7', '2', '5', '9', '6', '1', '6', '4', '7', '7', '3', '2', '8', '4', '2', '7', '0', '3', '4', '5', '7', '8', '2', '1', '2', '1', '6', '5', '5', '4', '2', '2', '5', '8', '1', '9', '6', '7', '7', '9', '1', '9', '0', '3', '2', '4', '1', '4', '2', '4', '8', '2', '4', '2', '1', '3', '7', '2', '1', '8', '0', '1', '3', '0', '8', '9', '1', '9', '5', '8', '3', '0', '0', '5', '7', '8', '1', '5', '4', '3', '8', '0', '0', '2', '6', '5', '5', '4', '7', '7', '9', '4', '4', '3', '5', '7', '2', '6', '6', '3', '2', '1', '8', '6', '3', '1', '7', '5', '9', '3', '2', '9', '8', '3', '4', '7']
noncomputable def geometryRow010_jensenBoundText : String := String.ofList (geometryRow010_jensenBoundNumeratorChars ++ '/' :: geometryRow010_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_jensenBound_before_field"
  err.flush

theorem geometryRow010_jensenBound_field :
    geometryRowsJson010.getObjVal? "jensen_bound" = .ok (.str geometryRow010_jensenBoundText) := by rfl

theorem geometryRow010_jensenBound_numerator_no_slash :
    geometryRow010_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow010_jensenBoundNumeratorChars = some (332644121498925507842224268834149130449387159614580303350578909864199469072583881190512000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow010_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow010_jensenBoundDenominatorChars = some (1569230072596164773284270345782121655422581967791903241424824213721801308919583005781543800265547794435726632186317593298347 : Int) := by decide +kernel

theorem geometryRow010_jensenBound_denominator_nonzero : (1569230072596164773284270345782121655422581967791903241424824213721801308919583005781543800265547794435726632186317593298347 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_jensenBound_parse :
    parseRational geometryRow010_jensenBoundText = .ok geometryRowsTyped010.jensenBound :=
  original_rational_fraction_of_chars geometryRow010_jensenBoundNumeratorChars geometryRow010_jensenBoundDenominatorChars
    (332644121498925507842224268834149130449387159614580303350578909864199469072583881190512000000000000000000000000 : Int) (1569230072596164773284270345782121655422581967791903241424824213721801308919583005781543800265547794435726632186317593298347 : Int)
    geometryRow010_jensenBound_numerator_no_slash geometryRow010_jensenBound_numerator_parse
    geometryRow010_jensenBound_denominator_parse geometryRow010_jensenBound_denominator_nonzero

theorem geometryRow010_jensenBound_read :
    rationalField geometryRowsJson010 "jensen_bound" = .ok geometryRowsTyped010.jensenBound :=
  original_rationalField_of_string geometryRowsJson010 "jensen_bound" geometryRow010_jensenBoundText
    geometryRowsTyped010.jensenBound geometryRow010_jensenBound_field geometryRow010_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_factorMaxima_before"
  err.flush

theorem geometryRow010_factorMaxima_read :
    rationalArrayField geometryRowsJson010 "factor_maxima" = .ok geometryRowsTyped010.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_gapWeightedMeans_before"
  err.flush

theorem geometryRow010_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson010 "gap_weighted_means" = .ok geometryRowsTyped010.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow010_floorChars : List Char := ['1', '6', '7', '9', '4', '7', '2', '1', '8', '0', '5', '1', '5', '2', '3', '1', '6']
noncomputable def geometryRow010_floorText : String := String.ofList geometryRow010_floorChars

theorem geometryRow010_floor_text_read :
    geometryRowsJson010.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow010_floorText := by rfl

theorem geometryRow010_floor_chars_parse :
    SourceJson.intChars geometryRow010_floorChars = some (16794721805152316 : Int) := by decide +kernel

theorem geometryRow010_floor_parse :
    parseInteger geometryRow010_floorText = .ok geometryRowsTyped010.jensenFloorQ96 := by
  simp only [geometryRow010_floorText, parseInteger, String.toList_ofList, geometryRow010_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_010 :
    decodeGeometryRow geometryRowsJson010 = .ok geometryRowsTyped010 :=
  original_geometryRow_of_fields geometryRowsJson010 geometryRowsTyped010 geometryRow010_floorText
    geometryRow010_simplexId_read geometryRow010_vertexIds_read
    geometryRow010_physicalVolume_read geometryRow010_meanGap_read
    geometryRow010_factorMaxima_read geometryRow010_gapWeightedMeans_read
    geometryRow010_jensenBound_read geometryRow010_floor_text_read geometryRow010_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_010_original_decoder_complete"
  err.flush

theorem geometryRow010_shape :
    geometryRowsTyped010.simplexId = 10 ∧
    geometryRowsTyped010.vertexIds.size = 9 ∧ geometryRowsTyped010.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped010.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped010.factorMaxima.size = 10 ∧ geometryRowsTyped010.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson011 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped011 : GeometryRow :=
  { simplexId := 11,
    vertexIds := #[27, 25, 11, 9, 8, 7, 5, 3, 1],
    physicalVolume := ((5210643984704373991005023183807002003 : ℚ) / (221217681678336000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((2399193300851 : ℚ) / (26132400000000 : ℚ)), ((2411798379281 : ℚ) / (26132400000000 : ℚ)), ((1241404692217 : ℚ) / (10452960000000 : ℚ)), ((4518162897991 : ℚ) / (52264800000000 : ℚ)), ((4340904330379 : ℚ) / (52264800000000 : ℚ)), ((787273776551 : ℚ) / (10452960000000 : ℚ)), ((1027131058343 : ℚ) / (26132400000000 : ℚ)), ((911291392297 : ℚ) / (26132400000000 : ℚ)), ((893509845157 : ℚ) / (26132400000000 : ℚ)), ((869692703207 : ℚ) / (26132400000000 : ℚ))],
    jensenBound := ((218175292215219845228398756609084540968919382938893631772131843128594411068116992000000000000000000000000 : ℚ) / (7334037391080042208184461213170550589430472120833049476747003360065029908582899749594539653597685068125856666672583451567 : ℚ)),
    jensenFloorQ96 := (2356904742433 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_simplexId_before"
  err.flush

theorem geometryRow011_simplexId_read :
    geometryRowsJson011.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped011.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_vertexIds_before"
  err.flush

theorem geometryRow011_vertexIds_read :
    geometryRowsJson011.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped011.vertexIds := by decide +kernel

noncomputable def geometryRow011_physicalVolumeNumeratorChars : List Char := ['5', '2', '1', '0', '6', '4', '3', '9', '8', '4', '7', '0', '4', '3', '7', '3', '9', '9', '1', '0', '0', '5', '0', '2', '3', '1', '8', '3', '8', '0', '7', '0', '0', '2', '0', '0', '3']
noncomputable def geometryRow011_physicalVolumeDenominatorChars : List Char := ['2', '2', '1', '2', '1', '7', '6', '8', '1', '6', '7', '8', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_physicalVolumeText : String := String.ofList (geometryRow011_physicalVolumeNumeratorChars ++ '/' :: geometryRow011_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_physicalVolume_before_field"
  err.flush

theorem geometryRow011_physicalVolume_field :
    geometryRowsJson011.getObjVal? "physical_volume" = .ok (.str geometryRow011_physicalVolumeText) := by rfl

theorem geometryRow011_physicalVolume_numerator_no_slash :
    geometryRow011_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow011_physicalVolumeNumeratorChars = some (5210643984704373991005023183807002003 : Int) := by decide +kernel

theorem geometryRow011_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow011_physicalVolumeDenominatorChars = some (221217681678336000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow011_physicalVolume_denominator_nonzero : (221217681678336000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_physicalVolume_parse :
    parseRational geometryRow011_physicalVolumeText = .ok geometryRowsTyped011.physicalVolume :=
  original_rational_fraction_of_chars geometryRow011_physicalVolumeNumeratorChars geometryRow011_physicalVolumeDenominatorChars
    (5210643984704373991005023183807002003 : Int) (221217681678336000000000000000000000000000000000000000000000000 : Int)
    geometryRow011_physicalVolume_numerator_no_slash geometryRow011_physicalVolume_numerator_parse
    geometryRow011_physicalVolume_denominator_parse geometryRow011_physicalVolume_denominator_nonzero

theorem geometryRow011_physicalVolume_read :
    rationalField geometryRowsJson011 "physical_volume" = .ok geometryRowsTyped011.physicalVolume :=
  original_rationalField_of_string geometryRowsJson011 "physical_volume" geometryRow011_physicalVolumeText
    geometryRowsTyped011.physicalVolume geometryRow011_physicalVolume_field geometryRow011_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_physicalVolume_complete"
  err.flush

noncomputable def geometryRow011_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow011_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_meanGapText : String := String.ofList (geometryRow011_meanGapNumeratorChars ++ '/' :: geometryRow011_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_meanGap_before_field"
  err.flush

theorem geometryRow011_meanGap_field :
    geometryRowsJson011.getObjVal? "mean_gap" = .ok (.str geometryRow011_meanGapText) := by rfl

theorem geometryRow011_meanGap_numerator_no_slash :
    geometryRow011_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_meanGap_numerator_parse :
    SourceJson.intChars geometryRow011_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow011_meanGap_denominator_parse :
    SourceJson.intChars geometryRow011_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow011_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_meanGap_parse :
    parseRational geometryRow011_meanGapText = .ok geometryRowsTyped011.meanGap :=
  original_rational_fraction_of_chars geometryRow011_meanGapNumeratorChars geometryRow011_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow011_meanGap_numerator_no_slash geometryRow011_meanGap_numerator_parse
    geometryRow011_meanGap_denominator_parse geometryRow011_meanGap_denominator_nonzero

theorem geometryRow011_meanGap_read :
    rationalField geometryRowsJson011 "mean_gap" = .ok geometryRowsTyped011.meanGap :=
  original_rationalField_of_string geometryRowsJson011 "mean_gap" geometryRow011_meanGapText
    geometryRowsTyped011.meanGap geometryRow011_meanGap_field geometryRow011_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_meanGap_complete"
  err.flush

noncomputable def geometryRow011_jensenBoundNumeratorChars : List Char := ['2', '1', '8', '1', '7', '5', '2', '9', '2', '2', '1', '5', '2', '1', '9', '8', '4', '5', '2', '2', '8', '3', '9', '8', '7', '5', '6', '6', '0', '9', '0', '8', '4', '5', '4', '0', '9', '6', '8', '9', '1', '9', '3', '8', '2', '9', '3', '8', '8', '9', '3', '6', '3', '1', '7', '7', '2', '1', '3', '1', '8', '4', '3', '1', '2', '8', '5', '9', '4', '4', '1', '1', '0', '6', '8', '1', '1', '6', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_jensenBoundDenominatorChars : List Char := ['7', '3', '3', '4', '0', '3', '7', '3', '9', '1', '0', '8', '0', '0', '4', '2', '2', '0', '8', '1', '8', '4', '4', '6', '1', '2', '1', '3', '1', '7', '0', '5', '5', '0', '5', '8', '9', '4', '3', '0', '4', '7', '2', '1', '2', '0', '8', '3', '3', '0', '4', '9', '4', '7', '6', '7', '4', '7', '0', '0', '3', '3', '6', '0', '0', '6', '5', '0', '2', '9', '9', '0', '8', '5', '8', '2', '8', '9', '9', '7', '4', '9', '5', '9', '4', '5', '3', '9', '6', '5', '3', '5', '9', '7', '6', '8', '5', '0', '6', '8', '1', '2', '5', '8', '5', '6', '6', '6', '6', '6', '7', '2', '5', '8', '3', '4', '5', '1', '5', '6', '7']
noncomputable def geometryRow011_jensenBoundText : String := String.ofList (geometryRow011_jensenBoundNumeratorChars ++ '/' :: geometryRow011_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_jensenBound_before_field"
  err.flush

theorem geometryRow011_jensenBound_field :
    geometryRowsJson011.getObjVal? "jensen_bound" = .ok (.str geometryRow011_jensenBoundText) := by rfl

theorem geometryRow011_jensenBound_numerator_no_slash :
    geometryRow011_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow011_jensenBoundNumeratorChars = some (218175292215219845228398756609084540968919382938893631772131843128594411068116992000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow011_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow011_jensenBoundDenominatorChars = some (7334037391080042208184461213170550589430472120833049476747003360065029908582899749594539653597685068125856666672583451567 : Int) := by decide +kernel

theorem geometryRow011_jensenBound_denominator_nonzero : (7334037391080042208184461213170550589430472120833049476747003360065029908582899749594539653597685068125856666672583451567 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_jensenBound_parse :
    parseRational geometryRow011_jensenBoundText = .ok geometryRowsTyped011.jensenBound :=
  original_rational_fraction_of_chars geometryRow011_jensenBoundNumeratorChars geometryRow011_jensenBoundDenominatorChars
    (218175292215219845228398756609084540968919382938893631772131843128594411068116992000000000000000000000000 : Int) (7334037391080042208184461213170550589430472120833049476747003360065029908582899749594539653597685068125856666672583451567 : Int)
    geometryRow011_jensenBound_numerator_no_slash geometryRow011_jensenBound_numerator_parse
    geometryRow011_jensenBound_denominator_parse geometryRow011_jensenBound_denominator_nonzero

theorem geometryRow011_jensenBound_read :
    rationalField geometryRowsJson011 "jensen_bound" = .ok geometryRowsTyped011.jensenBound :=
  original_rationalField_of_string geometryRowsJson011 "jensen_bound" geometryRow011_jensenBoundText
    geometryRowsTyped011.jensenBound geometryRow011_jensenBound_field geometryRow011_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_factorMaxima_before"
  err.flush

theorem geometryRow011_factorMaxima_read :
    rationalArrayField geometryRowsJson011 "factor_maxima" = .ok geometryRowsTyped011.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_gapWeightedMeans_before"
  err.flush

theorem geometryRow011_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson011 "gap_weighted_means" = .ok geometryRowsTyped011.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow011_floorChars : List Char := ['2', '3', '5', '6', '9', '0', '4', '7', '4', '2', '4', '3', '3']
noncomputable def geometryRow011_floorText : String := String.ofList geometryRow011_floorChars

theorem geometryRow011_floor_text_read :
    geometryRowsJson011.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow011_floorText := by rfl

theorem geometryRow011_floor_chars_parse :
    SourceJson.intChars geometryRow011_floorChars = some (2356904742433 : Int) := by decide +kernel

theorem geometryRow011_floor_parse :
    parseInteger geometryRow011_floorText = .ok geometryRowsTyped011.jensenFloorQ96 := by
  simp only [geometryRow011_floorText, parseInteger, String.toList_ofList, geometryRow011_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_011 :
    decodeGeometryRow geometryRowsJson011 = .ok geometryRowsTyped011 :=
  original_geometryRow_of_fields geometryRowsJson011 geometryRowsTyped011 geometryRow011_floorText
    geometryRow011_simplexId_read geometryRow011_vertexIds_read
    geometryRow011_physicalVolume_read geometryRow011_meanGap_read
    geometryRow011_factorMaxima_read geometryRow011_gapWeightedMeans_read
    geometryRow011_jensenBound_read geometryRow011_floor_text_read geometryRow011_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_011_original_decoder_complete"
  err.flush

theorem geometryRow011_shape :
    geometryRowsTyped011.simplexId = 11 ∧
    geometryRowsTyped011.vertexIds.size = 9 ∧ geometryRowsTyped011.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped011.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped011.factorMaxima.size = 10 ∧ geometryRowsTyped011.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson012 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped012 : GeometryRow :=
  { simplexId := 12,
    vertexIds := #[27, 25, 11, 10, 8, 7, 5, 3, 1],
    physicalVolume := ((1709221490032602904561388388514961736546011 : ℚ) / (7078965813706752000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((4834104474907 : ℚ) / (52264800000000 : ℚ)), ((4859314631767 : ℚ) / (52264800000000 : ℚ)), ((1241404692217 : ℚ) / (10452960000000 : ℚ)), ((1138469321719 : ℚ) / (13066200000000 : ℚ)), ((4340904330379 : ℚ) / (52264800000000 : ℚ)), ((787273776551 : ℚ) / (10452960000000 : ℚ)), ((1027131058343 : ℚ) / (26132400000000 : ℚ)), ((911291392297 : ℚ) / (26132400000000 : ℚ)), ((1751301817109 : ℚ) / (52264800000000 : ℚ)), ((1703671017529 : ℚ) / (52264800000000 : ℚ))],
    jensenBound := ((98404556389134363173933959164050667085167586668863839579370723674258115750310815559168000000000000000000000000 : ℚ) / (316855777367804498366346403364247059658233116729729730548893347736473739041889073286573537112781701603886478685293724634613 : ℚ)),
    jensenFloorQ96 := (24605554774822340 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_simplexId_before"
  err.flush

theorem geometryRow012_simplexId_read :
    geometryRowsJson012.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped012.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_vertexIds_before"
  err.flush

theorem geometryRow012_vertexIds_read :
    geometryRowsJson012.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped012.vertexIds := by decide +kernel

noncomputable def geometryRow012_physicalVolumeNumeratorChars : List Char := ['1', '7', '0', '9', '2', '2', '1', '4', '9', '0', '0', '3', '2', '6', '0', '2', '9', '0', '4', '5', '6', '1', '3', '8', '8', '3', '8', '8', '5', '1', '4', '9', '6', '1', '7', '3', '6', '5', '4', '6', '0', '1', '1']
noncomputable def geometryRow012_physicalVolumeDenominatorChars : List Char := ['7', '0', '7', '8', '9', '6', '5', '8', '1', '3', '7', '0', '6', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_physicalVolumeText : String := String.ofList (geometryRow012_physicalVolumeNumeratorChars ++ '/' :: geometryRow012_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_physicalVolume_before_field"
  err.flush

theorem geometryRow012_physicalVolume_field :
    geometryRowsJson012.getObjVal? "physical_volume" = .ok (.str geometryRow012_physicalVolumeText) := by rfl

theorem geometryRow012_physicalVolume_numerator_no_slash :
    geometryRow012_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow012_physicalVolumeNumeratorChars = some (1709221490032602904561388388514961736546011 : Int) := by decide +kernel

theorem geometryRow012_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow012_physicalVolumeDenominatorChars = some (7078965813706752000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow012_physicalVolume_denominator_nonzero : (7078965813706752000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_physicalVolume_parse :
    parseRational geometryRow012_physicalVolumeText = .ok geometryRowsTyped012.physicalVolume :=
  original_rational_fraction_of_chars geometryRow012_physicalVolumeNumeratorChars geometryRow012_physicalVolumeDenominatorChars
    (1709221490032602904561388388514961736546011 : Int) (7078965813706752000000000000000000000000000000000000000000000000 : Int)
    geometryRow012_physicalVolume_numerator_no_slash geometryRow012_physicalVolume_numerator_parse
    geometryRow012_physicalVolume_denominator_parse geometryRow012_physicalVolume_denominator_nonzero

theorem geometryRow012_physicalVolume_read :
    rationalField geometryRowsJson012 "physical_volume" = .ok geometryRowsTyped012.physicalVolume :=
  original_rationalField_of_string geometryRowsJson012 "physical_volume" geometryRow012_physicalVolumeText
    geometryRowsTyped012.physicalVolume geometryRow012_physicalVolume_field geometryRow012_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_physicalVolume_complete"
  err.flush

noncomputable def geometryRow012_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow012_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_meanGapText : String := String.ofList (geometryRow012_meanGapNumeratorChars ++ '/' :: geometryRow012_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_meanGap_before_field"
  err.flush

theorem geometryRow012_meanGap_field :
    geometryRowsJson012.getObjVal? "mean_gap" = .ok (.str geometryRow012_meanGapText) := by rfl

theorem geometryRow012_meanGap_numerator_no_slash :
    geometryRow012_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_meanGap_numerator_parse :
    SourceJson.intChars geometryRow012_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow012_meanGap_denominator_parse :
    SourceJson.intChars geometryRow012_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow012_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_meanGap_parse :
    parseRational geometryRow012_meanGapText = .ok geometryRowsTyped012.meanGap :=
  original_rational_fraction_of_chars geometryRow012_meanGapNumeratorChars geometryRow012_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow012_meanGap_numerator_no_slash geometryRow012_meanGap_numerator_parse
    geometryRow012_meanGap_denominator_parse geometryRow012_meanGap_denominator_nonzero

theorem geometryRow012_meanGap_read :
    rationalField geometryRowsJson012 "mean_gap" = .ok geometryRowsTyped012.meanGap :=
  original_rationalField_of_string geometryRowsJson012 "mean_gap" geometryRow012_meanGapText
    geometryRowsTyped012.meanGap geometryRow012_meanGap_field geometryRow012_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_meanGap_complete"
  err.flush

noncomputable def geometryRow012_jensenBoundNumeratorChars : List Char := ['9', '8', '4', '0', '4', '5', '5', '6', '3', '8', '9', '1', '3', '4', '3', '6', '3', '1', '7', '3', '9', '3', '3', '9', '5', '9', '1', '6', '4', '0', '5', '0', '6', '6', '7', '0', '8', '5', '1', '6', '7', '5', '8', '6', '6', '6', '8', '8', '6', '3', '8', '3', '9', '5', '7', '9', '3', '7', '0', '7', '2', '3', '6', '7', '4', '2', '5', '8', '1', '1', '5', '7', '5', '0', '3', '1', '0', '8', '1', '5', '5', '5', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_jensenBoundDenominatorChars : List Char := ['3', '1', '6', '8', '5', '5', '7', '7', '7', '3', '6', '7', '8', '0', '4', '4', '9', '8', '3', '6', '6', '3', '4', '6', '4', '0', '3', '3', '6', '4', '2', '4', '7', '0', '5', '9', '6', '5', '8', '2', '3', '3', '1', '1', '6', '7', '2', '9', '7', '2', '9', '7', '3', '0', '5', '4', '8', '8', '9', '3', '3', '4', '7', '7', '3', '6', '4', '7', '3', '7', '3', '9', '0', '4', '1', '8', '8', '9', '0', '7', '3', '2', '8', '6', '5', '7', '3', '5', '3', '7', '1', '1', '2', '7', '8', '1', '7', '0', '1', '6', '0', '3', '8', '8', '6', '4', '7', '8', '6', '8', '5', '2', '9', '3', '7', '2', '4', '6', '3', '4', '6', '1', '3']
noncomputable def geometryRow012_jensenBoundText : String := String.ofList (geometryRow012_jensenBoundNumeratorChars ++ '/' :: geometryRow012_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_jensenBound_before_field"
  err.flush

theorem geometryRow012_jensenBound_field :
    geometryRowsJson012.getObjVal? "jensen_bound" = .ok (.str geometryRow012_jensenBoundText) := by rfl

theorem geometryRow012_jensenBound_numerator_no_slash :
    geometryRow012_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow012_jensenBoundNumeratorChars = some (98404556389134363173933959164050667085167586668863839579370723674258115750310815559168000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow012_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow012_jensenBoundDenominatorChars = some (316855777367804498366346403364247059658233116729729730548893347736473739041889073286573537112781701603886478685293724634613 : Int) := by decide +kernel

theorem geometryRow012_jensenBound_denominator_nonzero : (316855777367804498366346403364247059658233116729729730548893347736473739041889073286573537112781701603886478685293724634613 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_jensenBound_parse :
    parseRational geometryRow012_jensenBoundText = .ok geometryRowsTyped012.jensenBound :=
  original_rational_fraction_of_chars geometryRow012_jensenBoundNumeratorChars geometryRow012_jensenBoundDenominatorChars
    (98404556389134363173933959164050667085167586668863839579370723674258115750310815559168000000000000000000000000 : Int) (316855777367804498366346403364247059658233116729729730548893347736473739041889073286573537112781701603886478685293724634613 : Int)
    geometryRow012_jensenBound_numerator_no_slash geometryRow012_jensenBound_numerator_parse
    geometryRow012_jensenBound_denominator_parse geometryRow012_jensenBound_denominator_nonzero

theorem geometryRow012_jensenBound_read :
    rationalField geometryRowsJson012 "jensen_bound" = .ok geometryRowsTyped012.jensenBound :=
  original_rationalField_of_string geometryRowsJson012 "jensen_bound" geometryRow012_jensenBoundText
    geometryRowsTyped012.jensenBound geometryRow012_jensenBound_field geometryRow012_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_factorMaxima_before"
  err.flush

theorem geometryRow012_factorMaxima_read :
    rationalArrayField geometryRowsJson012 "factor_maxima" = .ok geometryRowsTyped012.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_gapWeightedMeans_before"
  err.flush

theorem geometryRow012_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson012 "gap_weighted_means" = .ok geometryRowsTyped012.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow012_floorChars : List Char := ['2', '4', '6', '0', '5', '5', '5', '4', '7', '7', '4', '8', '2', '2', '3', '4', '0']
noncomputable def geometryRow012_floorText : String := String.ofList geometryRow012_floorChars

theorem geometryRow012_floor_text_read :
    geometryRowsJson012.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow012_floorText := by rfl

theorem geometryRow012_floor_chars_parse :
    SourceJson.intChars geometryRow012_floorChars = some (24605554774822340 : Int) := by decide +kernel

theorem geometryRow012_floor_parse :
    parseInteger geometryRow012_floorText = .ok geometryRowsTyped012.jensenFloorQ96 := by
  simp only [geometryRow012_floorText, parseInteger, String.toList_ofList, geometryRow012_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_012 :
    decodeGeometryRow geometryRowsJson012 = .ok geometryRowsTyped012 :=
  original_geometryRow_of_fields geometryRowsJson012 geometryRowsTyped012 geometryRow012_floorText
    geometryRow012_simplexId_read geometryRow012_vertexIds_read
    geometryRow012_physicalVolume_read geometryRow012_meanGap_read
    geometryRow012_factorMaxima_read geometryRow012_gapWeightedMeans_read
    geometryRow012_jensenBound_read geometryRow012_floor_text_read geometryRow012_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_012_original_decoder_complete"
  err.flush

theorem geometryRow012_shape :
    geometryRowsTyped012.simplexId = 12 ∧
    geometryRowsTyped012.vertexIds.size = 9 ∧ geometryRowsTyped012.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped012.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped012.factorMaxima.size = 10 ∧ geometryRowsTyped012.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson013 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped013 : GeometryRow :=
  { simplexId := 13,
    vertexIds := #[27, 25, 23, 11, 7, 5, 3, 1, 0],
    physicalVolume := ((204706512924278558182872105108581509 : ℚ) / (13250017392192000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((55069031707843 : ℚ) / (601045200000000 : ℚ)), ((55358948511733 : ℚ) / (601045200000000 : ℚ)), ((5745575692567 : ℚ) / (48083616000000 : ℚ)), ((107061051402233 : ℚ) / (1202090400000000 : ℚ)), ((102331080061397 : ℚ) / (1202090400000000 : ℚ)), ((17931726318829 : ℚ) / (240418080000000 : ℚ)), ((23991301864009 : ℚ) / (601045200000000 : ℚ)), ((20153488146101 : ℚ) / (601045200000000 : ℚ)), ((19418000419001 : ℚ) / (601045200000000 : ℚ)), ((18870206154151 : ℚ) / (601045200000000 : ℚ))],
    jensenBound := ((1185652904931214664867930697255229189241230759111398843650042258876792221965831817690617898598400000000000000000000000 : ℚ) / (55422038066437842637760634504257337072103615663326864961991567368003382183235035354809658532188292756413113066069825235967256916641673 : ℚ)),
    jensenFloorQ96 := (1694941296182 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_simplexId_before"
  err.flush

theorem geometryRow013_simplexId_read :
    geometryRowsJson013.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped013.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_vertexIds_before"
  err.flush

theorem geometryRow013_vertexIds_read :
    geometryRowsJson013.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped013.vertexIds := by decide +kernel

noncomputable def geometryRow013_physicalVolumeNumeratorChars : List Char := ['2', '0', '4', '7', '0', '6', '5', '1', '2', '9', '2', '4', '2', '7', '8', '5', '5', '8', '1', '8', '2', '8', '7', '2', '1', '0', '5', '1', '0', '8', '5', '8', '1', '5', '0', '9']
noncomputable def geometryRow013_physicalVolumeDenominatorChars : List Char := ['1', '3', '2', '5', '0', '0', '1', '7', '3', '9', '2', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow013_physicalVolumeText : String := String.ofList (geometryRow013_physicalVolumeNumeratorChars ++ '/' :: geometryRow013_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_physicalVolume_before_field"
  err.flush

theorem geometryRow013_physicalVolume_field :
    geometryRowsJson013.getObjVal? "physical_volume" = .ok (.str geometryRow013_physicalVolumeText) := by rfl

theorem geometryRow013_physicalVolume_numerator_no_slash :
    geometryRow013_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow013_physicalVolumeNumeratorChars = some (204706512924278558182872105108581509 : Int) := by decide +kernel

theorem geometryRow013_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow013_physicalVolumeDenominatorChars = some (13250017392192000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow013_physicalVolume_denominator_nonzero : (13250017392192000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_physicalVolume_parse :
    parseRational geometryRow013_physicalVolumeText = .ok geometryRowsTyped013.physicalVolume :=
  original_rational_fraction_of_chars geometryRow013_physicalVolumeNumeratorChars geometryRow013_physicalVolumeDenominatorChars
    (204706512924278558182872105108581509 : Int) (13250017392192000000000000000000000000000000000000000000000000 : Int)
    geometryRow013_physicalVolume_numerator_no_slash geometryRow013_physicalVolume_numerator_parse
    geometryRow013_physicalVolume_denominator_parse geometryRow013_physicalVolume_denominator_nonzero

theorem geometryRow013_physicalVolume_read :
    rationalField geometryRowsJson013 "physical_volume" = .ok geometryRowsTyped013.physicalVolume :=
  original_rationalField_of_string geometryRowsJson013 "physical_volume" geometryRow013_physicalVolumeText
    geometryRowsTyped013.physicalVolume geometryRow013_physicalVolume_field geometryRow013_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_physicalVolume_complete"
  err.flush

noncomputable def geometryRow013_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow013_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow013_meanGapText : String := String.ofList (geometryRow013_meanGapNumeratorChars ++ '/' :: geometryRow013_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_meanGap_before_field"
  err.flush

theorem geometryRow013_meanGap_field :
    geometryRowsJson013.getObjVal? "mean_gap" = .ok (.str geometryRow013_meanGapText) := by rfl

theorem geometryRow013_meanGap_numerator_no_slash :
    geometryRow013_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_meanGap_numerator_parse :
    SourceJson.intChars geometryRow013_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow013_meanGap_denominator_parse :
    SourceJson.intChars geometryRow013_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow013_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_meanGap_parse :
    parseRational geometryRow013_meanGapText = .ok geometryRowsTyped013.meanGap :=
  original_rational_fraction_of_chars geometryRow013_meanGapNumeratorChars geometryRow013_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow013_meanGap_numerator_no_slash geometryRow013_meanGap_numerator_parse
    geometryRow013_meanGap_denominator_parse geometryRow013_meanGap_denominator_nonzero

theorem geometryRow013_meanGap_read :
    rationalField geometryRowsJson013 "mean_gap" = .ok geometryRowsTyped013.meanGap :=
  original_rationalField_of_string geometryRowsJson013 "mean_gap" geometryRow013_meanGapText
    geometryRowsTyped013.meanGap geometryRow013_meanGap_field geometryRow013_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_meanGap_complete"
  err.flush

noncomputable def geometryRow013_jensenBoundNumeratorChars : List Char := ['1', '1', '8', '5', '6', '5', '2', '9', '0', '4', '9', '3', '1', '2', '1', '4', '6', '6', '4', '8', '6', '7', '9', '3', '0', '6', '9', '7', '2', '5', '5', '2', '2', '9', '1', '8', '9', '2', '4', '1', '2', '3', '0', '7', '5', '9', '1', '1', '1', '3', '9', '8', '8', '4', '3', '6', '5', '0', '0', '4', '2', '2', '5', '8', '8', '7', '6', '7', '9', '2', '2', '2', '1', '9', '6', '5', '8', '3', '1', '8', '1', '7', '6', '9', '0', '6', '1', '7', '8', '9', '8', '5', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow013_jensenBoundDenominatorChars : List Char := ['5', '5', '4', '2', '2', '0', '3', '8', '0', '6', '6', '4', '3', '7', '8', '4', '2', '6', '3', '7', '7', '6', '0', '6', '3', '4', '5', '0', '4', '2', '5', '7', '3', '3', '7', '0', '7', '2', '1', '0', '3', '6', '1', '5', '6', '6', '3', '3', '2', '6', '8', '6', '4', '9', '6', '1', '9', '9', '1', '5', '6', '7', '3', '6', '8', '0', '0', '3', '3', '8', '2', '1', '8', '3', '2', '3', '5', '0', '3', '5', '3', '5', '4', '8', '0', '9', '6', '5', '8', '5', '3', '2', '1', '8', '8', '2', '9', '2', '7', '5', '6', '4', '1', '3', '1', '1', '3', '0', '6', '6', '0', '6', '9', '8', '2', '5', '2', '3', '5', '9', '6', '7', '2', '5', '6', '9', '1', '6', '6', '4', '1', '6', '7', '3']
noncomputable def geometryRow013_jensenBoundText : String := String.ofList (geometryRow013_jensenBoundNumeratorChars ++ '/' :: geometryRow013_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_jensenBound_before_field"
  err.flush

theorem geometryRow013_jensenBound_field :
    geometryRowsJson013.getObjVal? "jensen_bound" = .ok (.str geometryRow013_jensenBoundText) := by rfl

theorem geometryRow013_jensenBound_numerator_no_slash :
    geometryRow013_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow013_jensenBoundNumeratorChars = some (1185652904931214664867930697255229189241230759111398843650042258876792221965831817690617898598400000000000000000000000 : Int) := by decide +kernel

theorem geometryRow013_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow013_jensenBoundDenominatorChars = some (55422038066437842637760634504257337072103615663326864961991567368003382183235035354809658532188292756413113066069825235967256916641673 : Int) := by decide +kernel

theorem geometryRow013_jensenBound_denominator_nonzero : (55422038066437842637760634504257337072103615663326864961991567368003382183235035354809658532188292756413113066069825235967256916641673 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_jensenBound_parse :
    parseRational geometryRow013_jensenBoundText = .ok geometryRowsTyped013.jensenBound :=
  original_rational_fraction_of_chars geometryRow013_jensenBoundNumeratorChars geometryRow013_jensenBoundDenominatorChars
    (1185652904931214664867930697255229189241230759111398843650042258876792221965831817690617898598400000000000000000000000 : Int) (55422038066437842637760634504257337072103615663326864961991567368003382183235035354809658532188292756413113066069825235967256916641673 : Int)
    geometryRow013_jensenBound_numerator_no_slash geometryRow013_jensenBound_numerator_parse
    geometryRow013_jensenBound_denominator_parse geometryRow013_jensenBound_denominator_nonzero

theorem geometryRow013_jensenBound_read :
    rationalField geometryRowsJson013 "jensen_bound" = .ok geometryRowsTyped013.jensenBound :=
  original_rationalField_of_string geometryRowsJson013 "jensen_bound" geometryRow013_jensenBoundText
    geometryRowsTyped013.jensenBound geometryRow013_jensenBound_field geometryRow013_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_factorMaxima_before"
  err.flush

theorem geometryRow013_factorMaxima_read :
    rationalArrayField geometryRowsJson013 "factor_maxima" = .ok geometryRowsTyped013.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_gapWeightedMeans_before"
  err.flush

theorem geometryRow013_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson013 "gap_weighted_means" = .ok geometryRowsTyped013.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow013_floorChars : List Char := ['1', '6', '9', '4', '9', '4', '1', '2', '9', '6', '1', '8', '2']
noncomputable def geometryRow013_floorText : String := String.ofList geometryRow013_floorChars

theorem geometryRow013_floor_text_read :
    geometryRowsJson013.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow013_floorText := by rfl

theorem geometryRow013_floor_chars_parse :
    SourceJson.intChars geometryRow013_floorChars = some (1694941296182 : Int) := by decide +kernel

theorem geometryRow013_floor_parse :
    parseInteger geometryRow013_floorText = .ok geometryRowsTyped013.jensenFloorQ96 := by
  simp only [geometryRow013_floorText, parseInteger, String.toList_ofList, geometryRow013_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_013 :
    decodeGeometryRow geometryRowsJson013 = .ok geometryRowsTyped013 :=
  original_geometryRow_of_fields geometryRowsJson013 geometryRowsTyped013 geometryRow013_floorText
    geometryRow013_simplexId_read geometryRow013_vertexIds_read
    geometryRow013_physicalVolume_read geometryRow013_meanGap_read
    geometryRow013_factorMaxima_read geometryRow013_gapWeightedMeans_read
    geometryRow013_jensenBound_read geometryRow013_floor_text_read geometryRow013_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_013_original_decoder_complete"
  err.flush

theorem geometryRow013_shape :
    geometryRowsTyped013.simplexId = 13 ∧
    geometryRowsTyped013.vertexIds.size = 9 ∧ geometryRowsTyped013.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped013.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped013.factorMaxima.size = 10 ∧ geometryRowsTyped013.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson014 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped014 : GeometryRow :=
  { simplexId := 14,
    vertexIds := #[27, 25, 23, 11, 7, 5, 3, 2, 0],
    physicalVolume := ((204711505750835166938532798145617581 : ℚ) / (13250017392192000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((13913937015457 : ℚ) / (150261300000000 : ℚ)), ((27972832432859 : ℚ) / (300522600000000 : ℚ)), ((14383496443217 : ℚ) / (120209040000000 : ℚ)), ((53432739642119 : ℚ) / (601045200000000 : ℚ)), ((51067753971701 : ℚ) / (601045200000000 : ℚ)), ((1789261189523 : ℚ) / (24041808000000 : ℚ)), ((11506700602177 : ℚ) / (300522600000000 : ℚ)), ((211969377751 : ℚ) / (6260887500000 : ℚ)), ((1634467717223 : ℚ) / (50087100000000 : ℚ)), ((9532889136073 : ℚ) / (300522600000000 : ℚ))],
    jensenBound := ((182748170056057415410110755901218768450757041179697017851556880510333183412833928055790400000000000000000000000 : ℚ) / (8584566038845369973145209487635835597613398090233868780407032880620604072268937178449396852557795522106543622612054778535270771 : ℚ)),
    jensenFloorQ96 := (1686608461146 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_simplexId_before"
  err.flush

theorem geometryRow014_simplexId_read :
    geometryRowsJson014.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped014.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_vertexIds_before"
  err.flush

theorem geometryRow014_vertexIds_read :
    geometryRowsJson014.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped014.vertexIds := by decide +kernel

noncomputable def geometryRow014_physicalVolumeNumeratorChars : List Char := ['2', '0', '4', '7', '1', '1', '5', '0', '5', '7', '5', '0', '8', '3', '5', '1', '6', '6', '9', '3', '8', '5', '3', '2', '7', '9', '8', '1', '4', '5', '6', '1', '7', '5', '8', '1']
noncomputable def geometryRow014_physicalVolumeDenominatorChars : List Char := ['1', '3', '2', '5', '0', '0', '1', '7', '3', '9', '2', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_physicalVolumeText : String := String.ofList (geometryRow014_physicalVolumeNumeratorChars ++ '/' :: geometryRow014_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_physicalVolume_before_field"
  err.flush

theorem geometryRow014_physicalVolume_field :
    geometryRowsJson014.getObjVal? "physical_volume" = .ok (.str geometryRow014_physicalVolumeText) := by rfl

theorem geometryRow014_physicalVolume_numerator_no_slash :
    geometryRow014_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow014_physicalVolumeNumeratorChars = some (204711505750835166938532798145617581 : Int) := by decide +kernel

theorem geometryRow014_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow014_physicalVolumeDenominatorChars = some (13250017392192000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow014_physicalVolume_denominator_nonzero : (13250017392192000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_physicalVolume_parse :
    parseRational geometryRow014_physicalVolumeText = .ok geometryRowsTyped014.physicalVolume :=
  original_rational_fraction_of_chars geometryRow014_physicalVolumeNumeratorChars geometryRow014_physicalVolumeDenominatorChars
    (204711505750835166938532798145617581 : Int) (13250017392192000000000000000000000000000000000000000000000000 : Int)
    geometryRow014_physicalVolume_numerator_no_slash geometryRow014_physicalVolume_numerator_parse
    geometryRow014_physicalVolume_denominator_parse geometryRow014_physicalVolume_denominator_nonzero

theorem geometryRow014_physicalVolume_read :
    rationalField geometryRowsJson014 "physical_volume" = .ok geometryRowsTyped014.physicalVolume :=
  original_rationalField_of_string geometryRowsJson014 "physical_volume" geometryRow014_physicalVolumeText
    geometryRowsTyped014.physicalVolume geometryRow014_physicalVolume_field geometryRow014_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_physicalVolume_complete"
  err.flush

noncomputable def geometryRow014_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow014_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_meanGapText : String := String.ofList (geometryRow014_meanGapNumeratorChars ++ '/' :: geometryRow014_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_meanGap_before_field"
  err.flush

theorem geometryRow014_meanGap_field :
    geometryRowsJson014.getObjVal? "mean_gap" = .ok (.str geometryRow014_meanGapText) := by rfl

theorem geometryRow014_meanGap_numerator_no_slash :
    geometryRow014_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_meanGap_numerator_parse :
    SourceJson.intChars geometryRow014_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow014_meanGap_denominator_parse :
    SourceJson.intChars geometryRow014_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow014_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_meanGap_parse :
    parseRational geometryRow014_meanGapText = .ok geometryRowsTyped014.meanGap :=
  original_rational_fraction_of_chars geometryRow014_meanGapNumeratorChars geometryRow014_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow014_meanGap_numerator_no_slash geometryRow014_meanGap_numerator_parse
    geometryRow014_meanGap_denominator_parse geometryRow014_meanGap_denominator_nonzero

theorem geometryRow014_meanGap_read :
    rationalField geometryRowsJson014 "mean_gap" = .ok geometryRowsTyped014.meanGap :=
  original_rationalField_of_string geometryRowsJson014 "mean_gap" geometryRow014_meanGapText
    geometryRowsTyped014.meanGap geometryRow014_meanGap_field geometryRow014_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_meanGap_complete"
  err.flush

noncomputable def geometryRow014_jensenBoundNumeratorChars : List Char := ['1', '8', '2', '7', '4', '8', '1', '7', '0', '0', '5', '6', '0', '5', '7', '4', '1', '5', '4', '1', '0', '1', '1', '0', '7', '5', '5', '9', '0', '1', '2', '1', '8', '7', '6', '8', '4', '5', '0', '7', '5', '7', '0', '4', '1', '1', '7', '9', '6', '9', '7', '0', '1', '7', '8', '5', '1', '5', '5', '6', '8', '8', '0', '5', '1', '0', '3', '3', '3', '1', '8', '3', '4', '1', '2', '8', '3', '3', '9', '2', '8', '0', '5', '5', '7', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_jensenBoundDenominatorChars : List Char := ['8', '5', '8', '4', '5', '6', '6', '0', '3', '8', '8', '4', '5', '3', '6', '9', '9', '7', '3', '1', '4', '5', '2', '0', '9', '4', '8', '7', '6', '3', '5', '8', '3', '5', '5', '9', '7', '6', '1', '3', '3', '9', '8', '0', '9', '0', '2', '3', '3', '8', '6', '8', '7', '8', '0', '4', '0', '7', '0', '3', '2', '8', '8', '0', '6', '2', '0', '6', '0', '4', '0', '7', '2', '2', '6', '8', '9', '3', '7', '1', '7', '8', '4', '4', '9', '3', '9', '6', '8', '5', '2', '5', '5', '7', '7', '9', '5', '5', '2', '2', '1', '0', '6', '5', '4', '3', '6', '2', '2', '6', '1', '2', '0', '5', '4', '7', '7', '8', '5', '3', '5', '2', '7', '0', '7', '7', '1']
noncomputable def geometryRow014_jensenBoundText : String := String.ofList (geometryRow014_jensenBoundNumeratorChars ++ '/' :: geometryRow014_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_jensenBound_before_field"
  err.flush

theorem geometryRow014_jensenBound_field :
    geometryRowsJson014.getObjVal? "jensen_bound" = .ok (.str geometryRow014_jensenBoundText) := by rfl

theorem geometryRow014_jensenBound_numerator_no_slash :
    geometryRow014_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow014_jensenBoundNumeratorChars = some (182748170056057415410110755901218768450757041179697017851556880510333183412833928055790400000000000000000000000 : Int) := by decide +kernel

theorem geometryRow014_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow014_jensenBoundDenominatorChars = some (8584566038845369973145209487635835597613398090233868780407032880620604072268937178449396852557795522106543622612054778535270771 : Int) := by decide +kernel

theorem geometryRow014_jensenBound_denominator_nonzero : (8584566038845369973145209487635835597613398090233868780407032880620604072268937178449396852557795522106543622612054778535270771 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_jensenBound_parse :
    parseRational geometryRow014_jensenBoundText = .ok geometryRowsTyped014.jensenBound :=
  original_rational_fraction_of_chars geometryRow014_jensenBoundNumeratorChars geometryRow014_jensenBoundDenominatorChars
    (182748170056057415410110755901218768450757041179697017851556880510333183412833928055790400000000000000000000000 : Int) (8584566038845369973145209487635835597613398090233868780407032880620604072268937178449396852557795522106543622612054778535270771 : Int)
    geometryRow014_jensenBound_numerator_no_slash geometryRow014_jensenBound_numerator_parse
    geometryRow014_jensenBound_denominator_parse geometryRow014_jensenBound_denominator_nonzero

theorem geometryRow014_jensenBound_read :
    rationalField geometryRowsJson014 "jensen_bound" = .ok geometryRowsTyped014.jensenBound :=
  original_rationalField_of_string geometryRowsJson014 "jensen_bound" geometryRow014_jensenBoundText
    geometryRowsTyped014.jensenBound geometryRow014_jensenBound_field geometryRow014_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_factorMaxima_before"
  err.flush

theorem geometryRow014_factorMaxima_read :
    rationalArrayField geometryRowsJson014 "factor_maxima" = .ok geometryRowsTyped014.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_gapWeightedMeans_before"
  err.flush

theorem geometryRow014_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson014 "gap_weighted_means" = .ok geometryRowsTyped014.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow014_floorChars : List Char := ['1', '6', '8', '6', '6', '0', '8', '4', '6', '1', '1', '4', '6']
noncomputable def geometryRow014_floorText : String := String.ofList geometryRow014_floorChars

theorem geometryRow014_floor_text_read :
    geometryRowsJson014.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow014_floorText := by rfl

theorem geometryRow014_floor_chars_parse :
    SourceJson.intChars geometryRow014_floorChars = some (1686608461146 : Int) := by decide +kernel

theorem geometryRow014_floor_parse :
    parseInteger geometryRow014_floorText = .ok geometryRowsTyped014.jensenFloorQ96 := by
  simp only [geometryRow014_floorText, parseInteger, String.toList_ofList, geometryRow014_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_014 :
    decodeGeometryRow geometryRowsJson014 = .ok geometryRowsTyped014 :=
  original_geometryRow_of_fields geometryRowsJson014 geometryRowsTyped014 geometryRow014_floorText
    geometryRow014_simplexId_read geometryRow014_vertexIds_read
    geometryRow014_physicalVolume_read geometryRow014_meanGap_read
    geometryRow014_factorMaxima_read geometryRow014_gapWeightedMeans_read
    geometryRow014_jensenBound_read geometryRow014_floor_text_read geometryRow014_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_014_original_decoder_complete"
  err.flush

theorem geometryRow014_shape :
    geometryRowsTyped014.simplexId = 14 ∧
    geometryRowsTyped014.vertexIds.size = 9 ∧ geometryRowsTyped014.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped014.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped014.factorMaxima.size = 10 ∧ geometryRowsTyped014.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson015 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped015 : GeometryRow :=
  { simplexId := 15,
    vertexIds := #[27, 25, 23, 11, 7, 5, 4, 2, 0],
    physicalVolume := ((22391685911216259691453405985090146353791 : ℚ) / (565334075400192000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((10824169 : ℚ) / (19584000000 : ℚ)),
    factorMaxima := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((2484299 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((4766873760415654000871 : ℚ) / (52046518571510400000000 : ℚ)), ((75089378707681080479 : ℚ) / (813226852679850000000 : ℚ)), ((207675661876397011597 : ℚ) / (1734883952383680000000 : ℚ)), ((194584641323898086677 : ℚ) / (2168604940479600000000 : ℚ)), ((30754132391695577253 : ℚ) / (361434156746600000000 : ℚ)), ((6405459797091545959 : ℚ) / (86744197619184000000 : ℚ)), ((337613129476540072933 : ℚ) / (8674419761918400000000 : ℚ)), ((879160136617769689051 : ℚ) / (26023259285755200000000 : ℚ)), ((849475820243130214531 : ℚ) / (26023259285755200000000 : ℚ)), ((8531434954725883271 : ℚ) / (271075617559950000000 : ℚ))],
    jensenBound := ((21095946138066112350824226009204767685982328348304738629392012130909357074678798399775059788567134524122030021398293356161427344011948663488364962386613834438644070400000000000000000000000 : ℚ) / (185740492854565580109579026505598044480274228479194879839139839775549370689046002819191998501672307991075016123632121699137537521074265814176333385961504950585960095291303024141787387185212695209290017 : ℚ)),
    jensenFloorQ96 := (8998538893334187 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_simplexId_before"
  err.flush

theorem geometryRow015_simplexId_read :
    geometryRowsJson015.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped015.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_vertexIds_before"
  err.flush

theorem geometryRow015_vertexIds_read :
    geometryRowsJson015.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped015.vertexIds := by decide +kernel

noncomputable def geometryRow015_physicalVolumeNumeratorChars : List Char := ['2', '2', '3', '9', '1', '6', '8', '5', '9', '1', '1', '2', '1', '6', '2', '5', '9', '6', '9', '1', '4', '5', '3', '4', '0', '5', '9', '8', '5', '0', '9', '0', '1', '4', '6', '3', '5', '3', '7', '9', '1']
noncomputable def geometryRow015_physicalVolumeDenominatorChars : List Char := ['5', '6', '5', '3', '3', '4', '0', '7', '5', '4', '0', '0', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_physicalVolumeText : String := String.ofList (geometryRow015_physicalVolumeNumeratorChars ++ '/' :: geometryRow015_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_physicalVolume_before_field"
  err.flush

theorem geometryRow015_physicalVolume_field :
    geometryRowsJson015.getObjVal? "physical_volume" = .ok (.str geometryRow015_physicalVolumeText) := by rfl

theorem geometryRow015_physicalVolume_numerator_no_slash :
    geometryRow015_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow015_physicalVolumeNumeratorChars = some (22391685911216259691453405985090146353791 : Int) := by decide +kernel

theorem geometryRow015_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow015_physicalVolumeDenominatorChars = some (565334075400192000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow015_physicalVolume_denominator_nonzero : (565334075400192000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_physicalVolume_parse :
    parseRational geometryRow015_physicalVolumeText = .ok geometryRowsTyped015.physicalVolume :=
  original_rational_fraction_of_chars geometryRow015_physicalVolumeNumeratorChars geometryRow015_physicalVolumeDenominatorChars
    (22391685911216259691453405985090146353791 : Int) (565334075400192000000000000000000000000000000000000000000000000 : Int)
    geometryRow015_physicalVolume_numerator_no_slash geometryRow015_physicalVolume_numerator_parse
    geometryRow015_physicalVolume_denominator_parse geometryRow015_physicalVolume_denominator_nonzero

theorem geometryRow015_physicalVolume_read :
    rationalField geometryRowsJson015 "physical_volume" = .ok geometryRowsTyped015.physicalVolume :=
  original_rationalField_of_string geometryRowsJson015 "physical_volume" geometryRow015_physicalVolumeText
    geometryRowsTyped015.physicalVolume geometryRow015_physicalVolume_field geometryRow015_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_physicalVolume_complete"
  err.flush

noncomputable def geometryRow015_meanGapNumeratorChars : List Char := ['1', '0', '8', '2', '4', '1', '6', '9']
noncomputable def geometryRow015_meanGapDenominatorChars : List Char := ['1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_meanGapText : String := String.ofList (geometryRow015_meanGapNumeratorChars ++ '/' :: geometryRow015_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_meanGap_before_field"
  err.flush

theorem geometryRow015_meanGap_field :
    geometryRowsJson015.getObjVal? "mean_gap" = .ok (.str geometryRow015_meanGapText) := by rfl

theorem geometryRow015_meanGap_numerator_no_slash :
    geometryRow015_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_meanGap_numerator_parse :
    SourceJson.intChars geometryRow015_meanGapNumeratorChars = some (10824169 : Int) := by decide +kernel

theorem geometryRow015_meanGap_denominator_parse :
    SourceJson.intChars geometryRow015_meanGapDenominatorChars = some (19584000000 : Int) := by decide +kernel

theorem geometryRow015_meanGap_denominator_nonzero : (19584000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_meanGap_parse :
    parseRational geometryRow015_meanGapText = .ok geometryRowsTyped015.meanGap :=
  original_rational_fraction_of_chars geometryRow015_meanGapNumeratorChars geometryRow015_meanGapDenominatorChars
    (10824169 : Int) (19584000000 : Int)
    geometryRow015_meanGap_numerator_no_slash geometryRow015_meanGap_numerator_parse
    geometryRow015_meanGap_denominator_parse geometryRow015_meanGap_denominator_nonzero

theorem geometryRow015_meanGap_read :
    rationalField geometryRowsJson015 "mean_gap" = .ok geometryRowsTyped015.meanGap :=
  original_rationalField_of_string geometryRowsJson015 "mean_gap" geometryRow015_meanGapText
    geometryRowsTyped015.meanGap geometryRow015_meanGap_field geometryRow015_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_meanGap_complete"
  err.flush

noncomputable def geometryRow015_jensenBoundNumeratorChars : List Char := ['2', '1', '0', '9', '5', '9', '4', '6', '1', '3', '8', '0', '6', '6', '1', '1', '2', '3', '5', '0', '8', '2', '4', '2', '2', '6', '0', '0', '9', '2', '0', '4', '7', '6', '7', '6', '8', '5', '9', '8', '2', '3', '2', '8', '3', '4', '8', '3', '0', '4', '7', '3', '8', '6', '2', '9', '3', '9', '2', '0', '1', '2', '1', '3', '0', '9', '0', '9', '3', '5', '7', '0', '7', '4', '6', '7', '8', '7', '9', '8', '3', '9', '9', '7', '7', '5', '0', '5', '9', '7', '8', '8', '5', '6', '7', '1', '3', '4', '5', '2', '4', '1', '2', '2', '0', '3', '0', '0', '2', '1', '3', '9', '8', '2', '9', '3', '3', '5', '6', '1', '6', '1', '4', '2', '7', '3', '4', '4', '0', '1', '1', '9', '4', '8', '6', '6', '3', '4', '8', '8', '3', '6', '4', '9', '6', '2', '3', '8', '6', '6', '1', '3', '8', '3', '4', '4', '3', '8', '6', '4', '4', '0', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_jensenBoundDenominatorChars : List Char := ['1', '8', '5', '7', '4', '0', '4', '9', '2', '8', '5', '4', '5', '6', '5', '5', '8', '0', '1', '0', '9', '5', '7', '9', '0', '2', '6', '5', '0', '5', '5', '9', '8', '0', '4', '4', '4', '8', '0', '2', '7', '4', '2', '2', '8', '4', '7', '9', '1', '9', '4', '8', '7', '9', '8', '3', '9', '1', '3', '9', '8', '3', '9', '7', '7', '5', '5', '4', '9', '3', '7', '0', '6', '8', '9', '0', '4', '6', '0', '0', '2', '8', '1', '9', '1', '9', '1', '9', '9', '8', '5', '0', '1', '6', '7', '2', '3', '0', '7', '9', '9', '1', '0', '7', '5', '0', '1', '6', '1', '2', '3', '6', '3', '2', '1', '2', '1', '6', '9', '9', '1', '3', '7', '5', '3', '7', '5', '2', '1', '0', '7', '4', '2', '6', '5', '8', '1', '4', '1', '7', '6', '3', '3', '3', '3', '8', '5', '9', '6', '1', '5', '0', '4', '9', '5', '0', '5', '8', '5', '9', '6', '0', '0', '9', '5', '2', '9', '1', '3', '0', '3', '0', '2', '4', '1', '4', '1', '7', '8', '7', '3', '8', '7', '1', '8', '5', '2', '1', '2', '6', '9', '5', '2', '0', '9', '2', '9', '0', '0', '1', '7']
noncomputable def geometryRow015_jensenBoundText : String := String.ofList (geometryRow015_jensenBoundNumeratorChars ++ '/' :: geometryRow015_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_jensenBound_before_field"
  err.flush

theorem geometryRow015_jensenBound_field :
    geometryRowsJson015.getObjVal? "jensen_bound" = .ok (.str geometryRow015_jensenBoundText) := by rfl

theorem geometryRow015_jensenBound_numerator_no_slash :
    geometryRow015_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow015_jensenBoundNumeratorChars = some (21095946138066112350824226009204767685982328348304738629392012130909357074678798399775059788567134524122030021398293356161427344011948663488364962386613834438644070400000000000000000000000 : Int) := by decide +kernel

theorem geometryRow015_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow015_jensenBoundDenominatorChars = some (185740492854565580109579026505598044480274228479194879839139839775549370689046002819191998501672307991075016123632121699137537521074265814176333385961504950585960095291303024141787387185212695209290017 : Int) := by decide +kernel

theorem geometryRow015_jensenBound_denominator_nonzero : (185740492854565580109579026505598044480274228479194879839139839775549370689046002819191998501672307991075016123632121699137537521074265814176333385961504950585960095291303024141787387185212695209290017 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_jensenBound_parse :
    parseRational geometryRow015_jensenBoundText = .ok geometryRowsTyped015.jensenBound :=
  original_rational_fraction_of_chars geometryRow015_jensenBoundNumeratorChars geometryRow015_jensenBoundDenominatorChars
    (21095946138066112350824226009204767685982328348304738629392012130909357074678798399775059788567134524122030021398293356161427344011948663488364962386613834438644070400000000000000000000000 : Int) (185740492854565580109579026505598044480274228479194879839139839775549370689046002819191998501672307991075016123632121699137537521074265814176333385961504950585960095291303024141787387185212695209290017 : Int)
    geometryRow015_jensenBound_numerator_no_slash geometryRow015_jensenBound_numerator_parse
    geometryRow015_jensenBound_denominator_parse geometryRow015_jensenBound_denominator_nonzero

theorem geometryRow015_jensenBound_read :
    rationalField geometryRowsJson015 "jensen_bound" = .ok geometryRowsTyped015.jensenBound :=
  original_rationalField_of_string geometryRowsJson015 "jensen_bound" geometryRow015_jensenBoundText
    geometryRowsTyped015.jensenBound geometryRow015_jensenBound_field geometryRow015_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_factorMaxima_before"
  err.flush

theorem geometryRow015_factorMaxima_read :
    rationalArrayField geometryRowsJson015 "factor_maxima" = .ok geometryRowsTyped015.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_gapWeightedMeans_before"
  err.flush

theorem geometryRow015_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson015 "gap_weighted_means" = .ok geometryRowsTyped015.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow015_floorChars : List Char := ['8', '9', '9', '8', '5', '3', '8', '8', '9', '3', '3', '3', '4', '1', '8', '7']
noncomputable def geometryRow015_floorText : String := String.ofList geometryRow015_floorChars

theorem geometryRow015_floor_text_read :
    geometryRowsJson015.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow015_floorText := by rfl

theorem geometryRow015_floor_chars_parse :
    SourceJson.intChars geometryRow015_floorChars = some (8998538893334187 : Int) := by decide +kernel

theorem geometryRow015_floor_parse :
    parseInteger geometryRow015_floorText = .ok geometryRowsTyped015.jensenFloorQ96 := by
  simp only [geometryRow015_floorText, parseInteger, String.toList_ofList, geometryRow015_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_015 :
    decodeGeometryRow geometryRowsJson015 = .ok geometryRowsTyped015 :=
  original_geometryRow_of_fields geometryRowsJson015 geometryRowsTyped015 geometryRow015_floorText
    geometryRow015_simplexId_read geometryRow015_vertexIds_read
    geometryRow015_physicalVolume_read geometryRow015_meanGap_read
    geometryRow015_factorMaxima_read geometryRow015_gapWeightedMeans_read
    geometryRow015_jensenBound_read geometryRow015_floor_text_read geometryRow015_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_015_original_decoder_complete"
  err.flush

theorem geometryRow015_shape :
    geometryRowsTyped015.simplexId = 15 ∧
    geometryRowsTyped015.vertexIds.size = 9 ∧ geometryRowsTyped015.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped015.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped015.factorMaxima.size = 10 ∧ geometryRowsTyped015.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock001 : List SourceJson := [geometryRowsJson008, geometryRowsJson009, geometryRowsJson010, geometryRowsJson011, geometryRowsJson012, geometryRowsJson013, geometryRowsJson014, geometryRowsJson015]
noncomputable def geometryRowsTypedBlock001 : List GeometryRow := [geometryRowsTyped008, geometryRowsTyped009, geometryRowsTyped010, geometryRowsTyped011, geometryRowsTyped012, geometryRowsTyped013, geometryRowsTyped014, geometryRowsTyped015]

theorem geometry_Rows_block_001_push_eq (acc : List SourceJson) :
    SimplicesBlock001.blockPush acc = [geometryRowsJson015, geometryRowsJson014, geometryRowsJson013, geometryRowsJson012, geometryRowsJson011, geometryRowsJson010, geometryRowsJson009, geometryRowsJson008] ++ acc := by rfl

theorem geometry_Rows_block_001_reverse (acc : List SourceJson) :
    (SimplicesBlock001.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock001 := by
  rw [geometry_Rows_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_001 :
    geometryRowsJsonBlock001.mapM decodeGeometryRow = .ok geometryRowsTypedBlock001 := by
  simp only [geometryRowsJsonBlock001, geometryRowsTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_008, decode_geometry_Rows_009, decode_geometry_Rows_010, decode_geometry_Rows_011, decode_geometry_Rows_012, decode_geometry_Rows_013, decode_geometry_Rows_014, decode_geometry_Rows_015]
  rfl

theorem geometry_Rows_block_001_length : geometryRowsTypedBlock001.length = 8 := by rfl

#print axioms geometryRow008_simplexId_read
#print axioms geometryRow008_vertexIds_read
#print axioms geometryRow008_physicalVolume_field
#print axioms geometryRow008_physicalVolume_numerator_no_slash
#print axioms geometryRow008_physicalVolume_numerator_parse
#print axioms geometryRow008_physicalVolume_denominator_parse
#print axioms geometryRow008_physicalVolume_denominator_nonzero
#print axioms geometryRow008_physicalVolume_parse
#print axioms geometryRow008_physicalVolume_read
#print axioms geometryRow008_meanGap_field
#print axioms geometryRow008_meanGap_numerator_no_slash
#print axioms geometryRow008_meanGap_numerator_parse
#print axioms geometryRow008_meanGap_denominator_parse
#print axioms geometryRow008_meanGap_denominator_nonzero
#print axioms geometryRow008_meanGap_parse
#print axioms geometryRow008_meanGap_read
#print axioms geometryRow008_jensenBound_field
#print axioms geometryRow008_jensenBound_numerator_no_slash
#print axioms geometryRow008_jensenBound_numerator_parse
#print axioms geometryRow008_jensenBound_denominator_parse
#print axioms geometryRow008_jensenBound_denominator_nonzero
#print axioms geometryRow008_jensenBound_parse
#print axioms geometryRow008_jensenBound_read
#print axioms geometryRow008_factorMaxima_read
#print axioms geometryRow008_gapWeightedMeans_read
#print axioms geometryRow008_floor_text_read
#print axioms geometryRow008_floor_chars_parse
#print axioms geometryRow008_floor_parse
#print axioms decode_geometry_Rows_008
#print axioms geometryRow008_shape
#print axioms geometryRow009_simplexId_read
#print axioms geometryRow009_vertexIds_read
#print axioms geometryRow009_physicalVolume_field
#print axioms geometryRow009_physicalVolume_numerator_no_slash
#print axioms geometryRow009_physicalVolume_numerator_parse
#print axioms geometryRow009_physicalVolume_denominator_parse
#print axioms geometryRow009_physicalVolume_denominator_nonzero
#print axioms geometryRow009_physicalVolume_parse
#print axioms geometryRow009_physicalVolume_read
#print axioms geometryRow009_meanGap_field
#print axioms geometryRow009_meanGap_numerator_no_slash
#print axioms geometryRow009_meanGap_numerator_parse
#print axioms geometryRow009_meanGap_denominator_parse
#print axioms geometryRow009_meanGap_denominator_nonzero
#print axioms geometryRow009_meanGap_parse
#print axioms geometryRow009_meanGap_read
#print axioms geometryRow009_jensenBound_field
#print axioms geometryRow009_jensenBound_numerator_no_slash
#print axioms geometryRow009_jensenBound_numerator_parse
#print axioms geometryRow009_jensenBound_denominator_parse
#print axioms geometryRow009_jensenBound_denominator_nonzero
#print axioms geometryRow009_jensenBound_parse
#print axioms geometryRow009_jensenBound_read
#print axioms geometryRow009_factorMaxima_read
#print axioms geometryRow009_gapWeightedMeans_read
#print axioms geometryRow009_floor_text_read
#print axioms geometryRow009_floor_chars_parse
#print axioms geometryRow009_floor_parse
#print axioms decode_geometry_Rows_009
#print axioms geometryRow009_shape
#print axioms geometryRow010_simplexId_read
#print axioms geometryRow010_vertexIds_read
#print axioms geometryRow010_physicalVolume_field
#print axioms geometryRow010_physicalVolume_numerator_no_slash
#print axioms geometryRow010_physicalVolume_numerator_parse
#print axioms geometryRow010_physicalVolume_denominator_parse
#print axioms geometryRow010_physicalVolume_denominator_nonzero
#print axioms geometryRow010_physicalVolume_parse
#print axioms geometryRow010_physicalVolume_read
#print axioms geometryRow010_meanGap_field
#print axioms geometryRow010_meanGap_numerator_no_slash
#print axioms geometryRow010_meanGap_numerator_parse
#print axioms geometryRow010_meanGap_denominator_parse
#print axioms geometryRow010_meanGap_denominator_nonzero
#print axioms geometryRow010_meanGap_parse
#print axioms geometryRow010_meanGap_read
#print axioms geometryRow010_jensenBound_field
#print axioms geometryRow010_jensenBound_numerator_no_slash
#print axioms geometryRow010_jensenBound_numerator_parse
#print axioms geometryRow010_jensenBound_denominator_parse
#print axioms geometryRow010_jensenBound_denominator_nonzero
#print axioms geometryRow010_jensenBound_parse
#print axioms geometryRow010_jensenBound_read
#print axioms geometryRow010_factorMaxima_read
#print axioms geometryRow010_gapWeightedMeans_read
#print axioms geometryRow010_floor_text_read
#print axioms geometryRow010_floor_chars_parse
#print axioms geometryRow010_floor_parse
#print axioms decode_geometry_Rows_010
#print axioms geometryRow010_shape
#print axioms geometryRow011_simplexId_read
#print axioms geometryRow011_vertexIds_read
#print axioms geometryRow011_physicalVolume_field
#print axioms geometryRow011_physicalVolume_numerator_no_slash
#print axioms geometryRow011_physicalVolume_numerator_parse
#print axioms geometryRow011_physicalVolume_denominator_parse
#print axioms geometryRow011_physicalVolume_denominator_nonzero
#print axioms geometryRow011_physicalVolume_parse
#print axioms geometryRow011_physicalVolume_read
#print axioms geometryRow011_meanGap_field
#print axioms geometryRow011_meanGap_numerator_no_slash
#print axioms geometryRow011_meanGap_numerator_parse
#print axioms geometryRow011_meanGap_denominator_parse
#print axioms geometryRow011_meanGap_denominator_nonzero
#print axioms geometryRow011_meanGap_parse
#print axioms geometryRow011_meanGap_read
#print axioms geometryRow011_jensenBound_field
#print axioms geometryRow011_jensenBound_numerator_no_slash
#print axioms geometryRow011_jensenBound_numerator_parse
#print axioms geometryRow011_jensenBound_denominator_parse
#print axioms geometryRow011_jensenBound_denominator_nonzero
#print axioms geometryRow011_jensenBound_parse
#print axioms geometryRow011_jensenBound_read
#print axioms geometryRow011_factorMaxima_read
#print axioms geometryRow011_gapWeightedMeans_read
#print axioms geometryRow011_floor_text_read
#print axioms geometryRow011_floor_chars_parse
#print axioms geometryRow011_floor_parse
#print axioms decode_geometry_Rows_011
#print axioms geometryRow011_shape
#print axioms geometryRow012_simplexId_read
#print axioms geometryRow012_vertexIds_read
#print axioms geometryRow012_physicalVolume_field
#print axioms geometryRow012_physicalVolume_numerator_no_slash
#print axioms geometryRow012_physicalVolume_numerator_parse
#print axioms geometryRow012_physicalVolume_denominator_parse
#print axioms geometryRow012_physicalVolume_denominator_nonzero
#print axioms geometryRow012_physicalVolume_parse
#print axioms geometryRow012_physicalVolume_read
#print axioms geometryRow012_meanGap_field
#print axioms geometryRow012_meanGap_numerator_no_slash
#print axioms geometryRow012_meanGap_numerator_parse
#print axioms geometryRow012_meanGap_denominator_parse
#print axioms geometryRow012_meanGap_denominator_nonzero
#print axioms geometryRow012_meanGap_parse
#print axioms geometryRow012_meanGap_read
#print axioms geometryRow012_jensenBound_field
#print axioms geometryRow012_jensenBound_numerator_no_slash
#print axioms geometryRow012_jensenBound_numerator_parse
#print axioms geometryRow012_jensenBound_denominator_parse
#print axioms geometryRow012_jensenBound_denominator_nonzero
#print axioms geometryRow012_jensenBound_parse
#print axioms geometryRow012_jensenBound_read
#print axioms geometryRow012_factorMaxima_read
#print axioms geometryRow012_gapWeightedMeans_read
#print axioms geometryRow012_floor_text_read
#print axioms geometryRow012_floor_chars_parse
#print axioms geometryRow012_floor_parse
#print axioms decode_geometry_Rows_012
#print axioms geometryRow012_shape
#print axioms geometryRow013_simplexId_read
#print axioms geometryRow013_vertexIds_read
#print axioms geometryRow013_physicalVolume_field
#print axioms geometryRow013_physicalVolume_numerator_no_slash
#print axioms geometryRow013_physicalVolume_numerator_parse
#print axioms geometryRow013_physicalVolume_denominator_parse
#print axioms geometryRow013_physicalVolume_denominator_nonzero
#print axioms geometryRow013_physicalVolume_parse
#print axioms geometryRow013_physicalVolume_read
#print axioms geometryRow013_meanGap_field
#print axioms geometryRow013_meanGap_numerator_no_slash
#print axioms geometryRow013_meanGap_numerator_parse
#print axioms geometryRow013_meanGap_denominator_parse
#print axioms geometryRow013_meanGap_denominator_nonzero
#print axioms geometryRow013_meanGap_parse
#print axioms geometryRow013_meanGap_read
#print axioms geometryRow013_jensenBound_field
#print axioms geometryRow013_jensenBound_numerator_no_slash
#print axioms geometryRow013_jensenBound_numerator_parse
#print axioms geometryRow013_jensenBound_denominator_parse
#print axioms geometryRow013_jensenBound_denominator_nonzero
#print axioms geometryRow013_jensenBound_parse
#print axioms geometryRow013_jensenBound_read
#print axioms geometryRow013_factorMaxima_read
#print axioms geometryRow013_gapWeightedMeans_read
#print axioms geometryRow013_floor_text_read
#print axioms geometryRow013_floor_chars_parse
#print axioms geometryRow013_floor_parse
#print axioms decode_geometry_Rows_013
#print axioms geometryRow013_shape
#print axioms geometryRow014_simplexId_read
#print axioms geometryRow014_vertexIds_read
#print axioms geometryRow014_physicalVolume_field
#print axioms geometryRow014_physicalVolume_numerator_no_slash
#print axioms geometryRow014_physicalVolume_numerator_parse
#print axioms geometryRow014_physicalVolume_denominator_parse
#print axioms geometryRow014_physicalVolume_denominator_nonzero
#print axioms geometryRow014_physicalVolume_parse
#print axioms geometryRow014_physicalVolume_read
#print axioms geometryRow014_meanGap_field
#print axioms geometryRow014_meanGap_numerator_no_slash
#print axioms geometryRow014_meanGap_numerator_parse
#print axioms geometryRow014_meanGap_denominator_parse
#print axioms geometryRow014_meanGap_denominator_nonzero
#print axioms geometryRow014_meanGap_parse
#print axioms geometryRow014_meanGap_read
#print axioms geometryRow014_jensenBound_field
#print axioms geometryRow014_jensenBound_numerator_no_slash
#print axioms geometryRow014_jensenBound_numerator_parse
#print axioms geometryRow014_jensenBound_denominator_parse
#print axioms geometryRow014_jensenBound_denominator_nonzero
#print axioms geometryRow014_jensenBound_parse
#print axioms geometryRow014_jensenBound_read
#print axioms geometryRow014_factorMaxima_read
#print axioms geometryRow014_gapWeightedMeans_read
#print axioms geometryRow014_floor_text_read
#print axioms geometryRow014_floor_chars_parse
#print axioms geometryRow014_floor_parse
#print axioms decode_geometry_Rows_014
#print axioms geometryRow014_shape
#print axioms geometryRow015_simplexId_read
#print axioms geometryRow015_vertexIds_read
#print axioms geometryRow015_physicalVolume_field
#print axioms geometryRow015_physicalVolume_numerator_no_slash
#print axioms geometryRow015_physicalVolume_numerator_parse
#print axioms geometryRow015_physicalVolume_denominator_parse
#print axioms geometryRow015_physicalVolume_denominator_nonzero
#print axioms geometryRow015_physicalVolume_parse
#print axioms geometryRow015_physicalVolume_read
#print axioms geometryRow015_meanGap_field
#print axioms geometryRow015_meanGap_numerator_no_slash
#print axioms geometryRow015_meanGap_numerator_parse
#print axioms geometryRow015_meanGap_denominator_parse
#print axioms geometryRow015_meanGap_denominator_nonzero
#print axioms geometryRow015_meanGap_parse
#print axioms geometryRow015_meanGap_read
#print axioms geometryRow015_jensenBound_field
#print axioms geometryRow015_jensenBound_numerator_no_slash
#print axioms geometryRow015_jensenBound_numerator_parse
#print axioms geometryRow015_jensenBound_denominator_parse
#print axioms geometryRow015_jensenBound_denominator_nonzero
#print axioms geometryRow015_jensenBound_parse
#print axioms geometryRow015_jensenBound_read
#print axioms geometryRow015_factorMaxima_read
#print axioms geometryRow015_gapWeightedMeans_read
#print axioms geometryRow015_floor_text_read
#print axioms geometryRow015_floor_chars_parse
#print axioms geometryRow015_floor_parse
#print axioms decode_geometry_Rows_015
#print axioms geometryRow015_shape
#print axioms geometry_Rows_block_001_push_eq
#print axioms geometry_Rows_block_001_reverse
#print axioms decode_geometry_Rows_block_001
#print axioms geometry_Rows_block_001_length

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
