import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock002

/-! Local typed certificates for original cell 06, rows 16 through 23.
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

noncomputable def geometryRowsJson016 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped016 : GeometryRow :=
  { simplexId := 16,
    vertexIds := #[32, 20, 18, 16, 14, 13, 10, 8, 0],
    physicalVolume := ((614442599298329502025235209006730969818421755439 : ℚ) / (337499536546529280000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((1668541409533 : ℚ) / (18572400000000 : ℚ)), ((1693071852337 : ℚ) / (18572400000000 : ℚ)), ((294762787887877 : ℚ) / (2562991200000000 : ℚ)), ((43908296317423 : ℚ) / (512598240000000 : ℚ)), ((217205655416591 : ℚ) / (2562991200000000 : ℚ)), ((17881299501409 : ℚ) / (232999200000000 : ℚ)), ((645389366203 : ℚ) / (16642800000000 : ℚ)), ((4290210027331 : ℚ) / (116499600000000 : ℚ)), ((4226808626611 : ℚ) / (116499600000000 : ℚ)), ((1782539880371 : ℚ) / (55717200000000 : ℚ))],
    jensenBound := ((423244088208267022865104017561093724813879335424581201524508948995503335147721111274503473905049600000000000000000000 : ℚ) / (68894661495421976537796528169230056783935282894717410261918216147004573957543607402898723497607355681574222216948660178186634699 : ℚ)),
    jensenFloorQ96 := (486726412118222759 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_simplexId_before"
  err.flush

theorem geometryRow016_simplexId_read :
    geometryRowsJson016.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped016.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_vertexIds_before"
  err.flush

theorem geometryRow016_vertexIds_read :
    geometryRowsJson016.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped016.vertexIds := by decide +kernel

noncomputable def geometryRow016_physicalVolumeNumeratorChars : List Char := ['6', '1', '4', '4', '4', '2', '5', '9', '9', '2', '9', '8', '3', '2', '9', '5', '0', '2', '0', '2', '5', '2', '3', '5', '2', '0', '9', '0', '0', '6', '7', '3', '0', '9', '6', '9', '8', '1', '8', '4', '2', '1', '7', '5', '5', '4', '3', '9']
noncomputable def geometryRow016_physicalVolumeDenominatorChars : List Char := ['3', '3', '7', '4', '9', '9', '5', '3', '6', '5', '4', '6', '5', '2', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_physicalVolumeText : String := String.ofList (geometryRow016_physicalVolumeNumeratorChars ++ '/' :: geometryRow016_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_physicalVolume_before_field"
  err.flush

theorem geometryRow016_physicalVolume_field :
    geometryRowsJson016.getObjVal? "physical_volume" = .ok (.str geometryRow016_physicalVolumeText) := by rfl

theorem geometryRow016_physicalVolume_numerator_no_slash :
    geometryRow016_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow016_physicalVolumeNumeratorChars = some (614442599298329502025235209006730969818421755439 : Int) := by decide +kernel

theorem geometryRow016_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow016_physicalVolumeDenominatorChars = some (337499536546529280000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow016_physicalVolume_denominator_nonzero : (337499536546529280000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_physicalVolume_parse :
    parseRational geometryRow016_physicalVolumeText = .ok geometryRowsTyped016.physicalVolume :=
  original_rational_fraction_of_chars geometryRow016_physicalVolumeNumeratorChars geometryRow016_physicalVolumeDenominatorChars
    (614442599298329502025235209006730969818421755439 : Int) (337499536546529280000000000000000000000000000000000000000000000000000 : Int)
    geometryRow016_physicalVolume_numerator_no_slash geometryRow016_physicalVolume_numerator_parse
    geometryRow016_physicalVolume_denominator_parse geometryRow016_physicalVolume_denominator_nonzero

theorem geometryRow016_physicalVolume_read :
    rationalField geometryRowsJson016 "physical_volume" = .ok geometryRowsTyped016.physicalVolume :=
  original_rationalField_of_string geometryRowsJson016 "physical_volume" geometryRow016_physicalVolumeText
    geometryRowsTyped016.physicalVolume geometryRow016_physicalVolume_field geometryRow016_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_physicalVolume_complete"
  err.flush

noncomputable def geometryRow016_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow016_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_meanGapText : String := String.ofList (geometryRow016_meanGapNumeratorChars ++ '/' :: geometryRow016_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_meanGap_before_field"
  err.flush

theorem geometryRow016_meanGap_field :
    geometryRowsJson016.getObjVal? "mean_gap" = .ok (.str geometryRow016_meanGapText) := by rfl

theorem geometryRow016_meanGap_numerator_no_slash :
    geometryRow016_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_meanGap_numerator_parse :
    SourceJson.intChars geometryRow016_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow016_meanGap_denominator_parse :
    SourceJson.intChars geometryRow016_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow016_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_meanGap_parse :
    parseRational geometryRow016_meanGapText = .ok geometryRowsTyped016.meanGap :=
  original_rational_fraction_of_chars geometryRow016_meanGapNumeratorChars geometryRow016_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow016_meanGap_numerator_no_slash geometryRow016_meanGap_numerator_parse
    geometryRow016_meanGap_denominator_parse geometryRow016_meanGap_denominator_nonzero

theorem geometryRow016_meanGap_read :
    rationalField geometryRowsJson016 "mean_gap" = .ok geometryRowsTyped016.meanGap :=
  original_rationalField_of_string geometryRowsJson016 "mean_gap" geometryRow016_meanGapText
    geometryRowsTyped016.meanGap geometryRow016_meanGap_field geometryRow016_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_meanGap_complete"
  err.flush

noncomputable def geometryRow016_jensenBoundNumeratorChars : List Char := ['4', '2', '3', '2', '4', '4', '0', '8', '8', '2', '0', '8', '2', '6', '7', '0', '2', '2', '8', '6', '5', '1', '0', '4', '0', '1', '7', '5', '6', '1', '0', '9', '3', '7', '2', '4', '8', '1', '3', '8', '7', '9', '3', '3', '5', '4', '2', '4', '5', '8', '1', '2', '0', '1', '5', '2', '4', '5', '0', '8', '9', '4', '8', '9', '9', '5', '5', '0', '3', '3', '3', '5', '1', '4', '7', '7', '2', '1', '1', '1', '1', '2', '7', '4', '5', '0', '3', '4', '7', '3', '9', '0', '5', '0', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_jensenBoundDenominatorChars : List Char := ['6', '8', '8', '9', '4', '6', '6', '1', '4', '9', '5', '4', '2', '1', '9', '7', '6', '5', '3', '7', '7', '9', '6', '5', '2', '8', '1', '6', '9', '2', '3', '0', '0', '5', '6', '7', '8', '3', '9', '3', '5', '2', '8', '2', '8', '9', '4', '7', '1', '7', '4', '1', '0', '2', '6', '1', '9', '1', '8', '2', '1', '6', '1', '4', '7', '0', '0', '4', '5', '7', '3', '9', '5', '7', '5', '4', '3', '6', '0', '7', '4', '0', '2', '8', '9', '8', '7', '2', '3', '4', '9', '7', '6', '0', '7', '3', '5', '5', '6', '8', '1', '5', '7', '4', '2', '2', '2', '2', '1', '6', '9', '4', '8', '6', '6', '0', '1', '7', '8', '1', '8', '6', '6', '3', '4', '6', '9', '9']
noncomputable def geometryRow016_jensenBoundText : String := String.ofList (geometryRow016_jensenBoundNumeratorChars ++ '/' :: geometryRow016_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_jensenBound_before_field"
  err.flush

theorem geometryRow016_jensenBound_field :
    geometryRowsJson016.getObjVal? "jensen_bound" = .ok (.str geometryRow016_jensenBoundText) := by rfl

theorem geometryRow016_jensenBound_numerator_no_slash :
    geometryRow016_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow016_jensenBoundNumeratorChars = some (423244088208267022865104017561093724813879335424581201524508948995503335147721111274503473905049600000000000000000000 : Int) := by decide +kernel

theorem geometryRow016_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow016_jensenBoundDenominatorChars = some (68894661495421976537796528169230056783935282894717410261918216147004573957543607402898723497607355681574222216948660178186634699 : Int) := by decide +kernel

theorem geometryRow016_jensenBound_denominator_nonzero : (68894661495421976537796528169230056783935282894717410261918216147004573957543607402898723497607355681574222216948660178186634699 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_jensenBound_parse :
    parseRational geometryRow016_jensenBoundText = .ok geometryRowsTyped016.jensenBound :=
  original_rational_fraction_of_chars geometryRow016_jensenBoundNumeratorChars geometryRow016_jensenBoundDenominatorChars
    (423244088208267022865104017561093724813879335424581201524508948995503335147721111274503473905049600000000000000000000 : Int) (68894661495421976537796528169230056783935282894717410261918216147004573957543607402898723497607355681574222216948660178186634699 : Int)
    geometryRow016_jensenBound_numerator_no_slash geometryRow016_jensenBound_numerator_parse
    geometryRow016_jensenBound_denominator_parse geometryRow016_jensenBound_denominator_nonzero

theorem geometryRow016_jensenBound_read :
    rationalField geometryRowsJson016 "jensen_bound" = .ok geometryRowsTyped016.jensenBound :=
  original_rationalField_of_string geometryRowsJson016 "jensen_bound" geometryRow016_jensenBoundText
    geometryRowsTyped016.jensenBound geometryRow016_jensenBound_field geometryRow016_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_factorMaxima_before"
  err.flush

theorem geometryRow016_factorMaxima_read :
    rationalArrayField geometryRowsJson016 "factor_maxima" = .ok geometryRowsTyped016.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_gapWeightedMeans_before"
  err.flush

theorem geometryRow016_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson016 "gap_weighted_means" = .ok geometryRowsTyped016.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow016_floorChars : List Char := ['4', '8', '6', '7', '2', '6', '4', '1', '2', '1', '1', '8', '2', '2', '2', '7', '5', '9']
noncomputable def geometryRow016_floorText : String := String.ofList geometryRow016_floorChars

theorem geometryRow016_floor_text_read :
    geometryRowsJson016.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow016_floorText := by rfl

theorem geometryRow016_floor_chars_parse :
    SourceJson.intChars geometryRow016_floorChars = some (486726412118222759 : Int) := by decide +kernel

theorem geometryRow016_floor_parse :
    parseInteger geometryRow016_floorText = .ok geometryRowsTyped016.jensenFloorQ96 := by
  simp only [geometryRow016_floorText, parseInteger, String.toList_ofList, geometryRow016_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_016 :
    decodeGeometryRow geometryRowsJson016 = .ok geometryRowsTyped016 :=
  original_geometryRow_of_fields geometryRowsJson016 geometryRowsTyped016 geometryRow016_floorText
    geometryRow016_simplexId_read geometryRow016_vertexIds_read
    geometryRow016_physicalVolume_read geometryRow016_meanGap_read
    geometryRow016_factorMaxima_read geometryRow016_gapWeightedMeans_read
    geometryRow016_jensenBound_read geometryRow016_floor_text_read geometryRow016_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_016_original_decoder_complete"
  err.flush

theorem geometryRow016_shape :
    geometryRowsTyped016.simplexId = 16 ∧
    geometryRowsTyped016.vertexIds.size = 9 ∧ geometryRowsTyped016.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped016.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped016.factorMaxima.size = 10 ∧ geometryRowsTyped016.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson017 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped017 : GeometryRow :=
  { simplexId := 17,
    vertexIds := #[32, 20, 18, 17, 16, 14, 12, 11, 7],
    physicalVolume := ((386676257227107795765731330474762749967 : ℚ) / (3578452770816000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((182269 : ℚ) / (264000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((1704862987769 : ℚ) / (18572400000000 : ℚ)), ((1727943711239 : ℚ) / (18572400000000 : ℚ)), ((4299253273517 : ℚ) / (37144800000000 : ℚ)), ((3146190903059 : ℚ) / (37144800000000 : ℚ)), ((345815372207 : ℚ) / (4127200000000 : ℚ)), ((2848035802963 : ℚ) / (37144800000000 : ℚ)), ((25698754999 : ℚ) / (663300000000 : ℚ)), ((341647715831 : ℚ) / (9286200000000 : ℚ)), ((639659768047 : ℚ) / (18572400000000 : ℚ)), ((69192197441 : ℚ) / (2063600000000 : ℚ))],
    jensenBound := ((395371138035966295907907259013978497801990575818961545887303735732329462855954600000000000000000000000 : ℚ) / (1173114295347998549301512107662740369629028063904763616654658802542930882647567350318612981547448172601081051545619543 : ℚ)),
    jensenFloorQ96 := (26702026308929 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_simplexId_before"
  err.flush

theorem geometryRow017_simplexId_read :
    geometryRowsJson017.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped017.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_vertexIds_before"
  err.flush

theorem geometryRow017_vertexIds_read :
    geometryRowsJson017.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped017.vertexIds := by decide +kernel

noncomputable def geometryRow017_physicalVolumeNumeratorChars : List Char := ['3', '8', '6', '6', '7', '6', '2', '5', '7', '2', '2', '7', '1', '0', '7', '7', '9', '5', '7', '6', '5', '7', '3', '1', '3', '3', '0', '4', '7', '4', '7', '6', '2', '7', '4', '9', '9', '6', '7']
noncomputable def geometryRow017_physicalVolumeDenominatorChars : List Char := ['3', '5', '7', '8', '4', '5', '2', '7', '7', '0', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow017_physicalVolumeText : String := String.ofList (geometryRow017_physicalVolumeNumeratorChars ++ '/' :: geometryRow017_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_physicalVolume_before_field"
  err.flush

theorem geometryRow017_physicalVolume_field :
    geometryRowsJson017.getObjVal? "physical_volume" = .ok (.str geometryRow017_physicalVolumeText) := by rfl

theorem geometryRow017_physicalVolume_numerator_no_slash :
    geometryRow017_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow017_physicalVolumeNumeratorChars = some (386676257227107795765731330474762749967 : Int) := by decide +kernel

theorem geometryRow017_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow017_physicalVolumeDenominatorChars = some (3578452770816000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow017_physicalVolume_denominator_nonzero : (3578452770816000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_physicalVolume_parse :
    parseRational geometryRow017_physicalVolumeText = .ok geometryRowsTyped017.physicalVolume :=
  original_rational_fraction_of_chars geometryRow017_physicalVolumeNumeratorChars geometryRow017_physicalVolumeDenominatorChars
    (386676257227107795765731330474762749967 : Int) (3578452770816000000000000000000000000000000000000000000000000000 : Int)
    geometryRow017_physicalVolume_numerator_no_slash geometryRow017_physicalVolume_numerator_parse
    geometryRow017_physicalVolume_denominator_parse geometryRow017_physicalVolume_denominator_nonzero

theorem geometryRow017_physicalVolume_read :
    rationalField geometryRowsJson017 "physical_volume" = .ok geometryRowsTyped017.physicalVolume :=
  original_rationalField_of_string geometryRowsJson017 "physical_volume" geometryRow017_physicalVolumeText
    geometryRowsTyped017.physicalVolume geometryRow017_physicalVolume_field geometryRow017_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_physicalVolume_complete"
  err.flush

noncomputable def geometryRow017_meanGapNumeratorChars : List Char := ['1', '8', '2', '2', '6', '9']
noncomputable def geometryRow017_meanGapDenominatorChars : List Char := ['2', '6', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow017_meanGapText : String := String.ofList (geometryRow017_meanGapNumeratorChars ++ '/' :: geometryRow017_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_meanGap_before_field"
  err.flush

theorem geometryRow017_meanGap_field :
    geometryRowsJson017.getObjVal? "mean_gap" = .ok (.str geometryRow017_meanGapText) := by rfl

theorem geometryRow017_meanGap_numerator_no_slash :
    geometryRow017_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_meanGap_numerator_parse :
    SourceJson.intChars geometryRow017_meanGapNumeratorChars = some (182269 : Int) := by decide +kernel

theorem geometryRow017_meanGap_denominator_parse :
    SourceJson.intChars geometryRow017_meanGapDenominatorChars = some (264000000 : Int) := by decide +kernel

theorem geometryRow017_meanGap_denominator_nonzero : (264000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_meanGap_parse :
    parseRational geometryRow017_meanGapText = .ok geometryRowsTyped017.meanGap :=
  original_rational_fraction_of_chars geometryRow017_meanGapNumeratorChars geometryRow017_meanGapDenominatorChars
    (182269 : Int) (264000000 : Int)
    geometryRow017_meanGap_numerator_no_slash geometryRow017_meanGap_numerator_parse
    geometryRow017_meanGap_denominator_parse geometryRow017_meanGap_denominator_nonzero

theorem geometryRow017_meanGap_read :
    rationalField geometryRowsJson017 "mean_gap" = .ok geometryRowsTyped017.meanGap :=
  original_rationalField_of_string geometryRowsJson017 "mean_gap" geometryRow017_meanGapText
    geometryRowsTyped017.meanGap geometryRow017_meanGap_field geometryRow017_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_meanGap_complete"
  err.flush

noncomputable def geometryRow017_jensenBoundNumeratorChars : List Char := ['3', '9', '5', '3', '7', '1', '1', '3', '8', '0', '3', '5', '9', '6', '6', '2', '9', '5', '9', '0', '7', '9', '0', '7', '2', '5', '9', '0', '1', '3', '9', '7', '8', '4', '9', '7', '8', '0', '1', '9', '9', '0', '5', '7', '5', '8', '1', '8', '9', '6', '1', '5', '4', '5', '8', '8', '7', '3', '0', '3', '7', '3', '5', '7', '3', '2', '3', '2', '9', '4', '6', '2', '8', '5', '5', '9', '5', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow017_jensenBoundDenominatorChars : List Char := ['1', '1', '7', '3', '1', '1', '4', '2', '9', '5', '3', '4', '7', '9', '9', '8', '5', '4', '9', '3', '0', '1', '5', '1', '2', '1', '0', '7', '6', '6', '2', '7', '4', '0', '3', '6', '9', '6', '2', '9', '0', '2', '8', '0', '6', '3', '9', '0', '4', '7', '6', '3', '6', '1', '6', '6', '5', '4', '6', '5', '8', '8', '0', '2', '5', '4', '2', '9', '3', '0', '8', '8', '2', '6', '4', '7', '5', '6', '7', '3', '5', '0', '3', '1', '8', '6', '1', '2', '9', '8', '1', '5', '4', '7', '4', '4', '8', '1', '7', '2', '6', '0', '1', '0', '8', '1', '0', '5', '1', '5', '4', '5', '6', '1', '9', '5', '4', '3']
noncomputable def geometryRow017_jensenBoundText : String := String.ofList (geometryRow017_jensenBoundNumeratorChars ++ '/' :: geometryRow017_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_jensenBound_before_field"
  err.flush

theorem geometryRow017_jensenBound_field :
    geometryRowsJson017.getObjVal? "jensen_bound" = .ok (.str geometryRow017_jensenBoundText) := by rfl

theorem geometryRow017_jensenBound_numerator_no_slash :
    geometryRow017_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow017_jensenBoundNumeratorChars = some (395371138035966295907907259013978497801990575818961545887303735732329462855954600000000000000000000000 : Int) := by decide +kernel

theorem geometryRow017_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow017_jensenBoundDenominatorChars = some (1173114295347998549301512107662740369629028063904763616654658802542930882647567350318612981547448172601081051545619543 : Int) := by decide +kernel

theorem geometryRow017_jensenBound_denominator_nonzero : (1173114295347998549301512107662740369629028063904763616654658802542930882647567350318612981547448172601081051545619543 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_jensenBound_parse :
    parseRational geometryRow017_jensenBoundText = .ok geometryRowsTyped017.jensenBound :=
  original_rational_fraction_of_chars geometryRow017_jensenBoundNumeratorChars geometryRow017_jensenBoundDenominatorChars
    (395371138035966295907907259013978497801990575818961545887303735732329462855954600000000000000000000000 : Int) (1173114295347998549301512107662740369629028063904763616654658802542930882647567350318612981547448172601081051545619543 : Int)
    geometryRow017_jensenBound_numerator_no_slash geometryRow017_jensenBound_numerator_parse
    geometryRow017_jensenBound_denominator_parse geometryRow017_jensenBound_denominator_nonzero

theorem geometryRow017_jensenBound_read :
    rationalField geometryRowsJson017 "jensen_bound" = .ok geometryRowsTyped017.jensenBound :=
  original_rationalField_of_string geometryRowsJson017 "jensen_bound" geometryRow017_jensenBoundText
    geometryRowsTyped017.jensenBound geometryRow017_jensenBound_field geometryRow017_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_factorMaxima_before"
  err.flush

theorem geometryRow017_factorMaxima_read :
    rationalArrayField geometryRowsJson017 "factor_maxima" = .ok geometryRowsTyped017.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_gapWeightedMeans_before"
  err.flush

theorem geometryRow017_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson017 "gap_weighted_means" = .ok geometryRowsTyped017.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow017_floorChars : List Char := ['2', '6', '7', '0', '2', '0', '2', '6', '3', '0', '8', '9', '2', '9']
noncomputable def geometryRow017_floorText : String := String.ofList geometryRow017_floorChars

theorem geometryRow017_floor_text_read :
    geometryRowsJson017.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow017_floorText := by rfl

theorem geometryRow017_floor_chars_parse :
    SourceJson.intChars geometryRow017_floorChars = some (26702026308929 : Int) := by decide +kernel

theorem geometryRow017_floor_parse :
    parseInteger geometryRow017_floorText = .ok geometryRowsTyped017.jensenFloorQ96 := by
  simp only [geometryRow017_floorText, parseInteger, String.toList_ofList, geometryRow017_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_017 :
    decodeGeometryRow geometryRowsJson017 = .ok geometryRowsTyped017 :=
  original_geometryRow_of_fields geometryRowsJson017 geometryRowsTyped017 geometryRow017_floorText
    geometryRow017_simplexId_read geometryRow017_vertexIds_read
    geometryRow017_physicalVolume_read geometryRow017_meanGap_read
    geometryRow017_factorMaxima_read geometryRow017_gapWeightedMeans_read
    geometryRow017_jensenBound_read geometryRow017_floor_text_read geometryRow017_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_017_original_decoder_complete"
  err.flush

theorem geometryRow017_shape :
    geometryRowsTyped017.simplexId = 17 ∧
    geometryRowsTyped017.vertexIds.size = 9 ∧ geometryRowsTyped017.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped017.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped017.factorMaxima.size = 10 ∧ geometryRowsTyped017.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson018 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped018 : GeometryRow :=
  { simplexId := 18,
    vertexIds := #[32, 20, 19, 17, 16, 14, 12, 11, 7],
    physicalVolume := ((70484250286244366891578434322175536558216283 : ℚ) / (63616938147840000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((182269 : ℚ) / (264000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((137404689907 : ℚ) / (1485792000000 : ℚ)), ((696255738923 : ℚ) / (7428960000000 : ℚ)), ((4299253273517 : ℚ) / (37144800000000 : ℚ)), ((792894924719 : ℚ) / (9286200000000 : ℚ)), ((345815372207 : ℚ) / (4127200000000 : ℚ)), ((2848035802963 : ℚ) / (37144800000000 : ℚ)), ((25698754999 : ℚ) / (663300000000 : ℚ)), ((341647715831 : ℚ) / (9286200000000 : ℚ)), ((1253928263957 : ℚ) / (37144800000000 : ℚ)), ((135563417569 : ℚ) / (4127200000000 : ℚ))],
    jensenBound := ((129724512201560710910413457565234713943489842021335172593731993834526832338058188431720000000000000000000 : ℚ) / (36874930103630907952062832799407972871714504420254691329296130734462090151534741764966158831019189288613393627221967 : ℚ)),
    jensenFloorQ96 := (278721470275462488 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_simplexId_before"
  err.flush

theorem geometryRow018_simplexId_read :
    geometryRowsJson018.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped018.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_vertexIds_before"
  err.flush

theorem geometryRow018_vertexIds_read :
    geometryRowsJson018.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped018.vertexIds := by decide +kernel

noncomputable def geometryRow018_physicalVolumeNumeratorChars : List Char := ['7', '0', '4', '8', '4', '2', '5', '0', '2', '8', '6', '2', '4', '4', '3', '6', '6', '8', '9', '1', '5', '7', '8', '4', '3', '4', '3', '2', '2', '1', '7', '5', '5', '3', '6', '5', '5', '8', '2', '1', '6', '2', '8', '3']
noncomputable def geometryRow018_physicalVolumeDenominatorChars : List Char := ['6', '3', '6', '1', '6', '9', '3', '8', '1', '4', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_physicalVolumeText : String := String.ofList (geometryRow018_physicalVolumeNumeratorChars ++ '/' :: geometryRow018_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_physicalVolume_before_field"
  err.flush

theorem geometryRow018_physicalVolume_field :
    geometryRowsJson018.getObjVal? "physical_volume" = .ok (.str geometryRow018_physicalVolumeText) := by rfl

theorem geometryRow018_physicalVolume_numerator_no_slash :
    geometryRow018_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow018_physicalVolumeNumeratorChars = some (70484250286244366891578434322175536558216283 : Int) := by decide +kernel

theorem geometryRow018_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow018_physicalVolumeDenominatorChars = some (63616938147840000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow018_physicalVolume_denominator_nonzero : (63616938147840000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_physicalVolume_parse :
    parseRational geometryRow018_physicalVolumeText = .ok geometryRowsTyped018.physicalVolume :=
  original_rational_fraction_of_chars geometryRow018_physicalVolumeNumeratorChars geometryRow018_physicalVolumeDenominatorChars
    (70484250286244366891578434322175536558216283 : Int) (63616938147840000000000000000000000000000000000000000000000000000 : Int)
    geometryRow018_physicalVolume_numerator_no_slash geometryRow018_physicalVolume_numerator_parse
    geometryRow018_physicalVolume_denominator_parse geometryRow018_physicalVolume_denominator_nonzero

theorem geometryRow018_physicalVolume_read :
    rationalField geometryRowsJson018 "physical_volume" = .ok geometryRowsTyped018.physicalVolume :=
  original_rationalField_of_string geometryRowsJson018 "physical_volume" geometryRow018_physicalVolumeText
    geometryRowsTyped018.physicalVolume geometryRow018_physicalVolume_field geometryRow018_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_physicalVolume_complete"
  err.flush

noncomputable def geometryRow018_meanGapNumeratorChars : List Char := ['1', '8', '2', '2', '6', '9']
noncomputable def geometryRow018_meanGapDenominatorChars : List Char := ['2', '6', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_meanGapText : String := String.ofList (geometryRow018_meanGapNumeratorChars ++ '/' :: geometryRow018_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_meanGap_before_field"
  err.flush

theorem geometryRow018_meanGap_field :
    geometryRowsJson018.getObjVal? "mean_gap" = .ok (.str geometryRow018_meanGapText) := by rfl

theorem geometryRow018_meanGap_numerator_no_slash :
    geometryRow018_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_meanGap_numerator_parse :
    SourceJson.intChars geometryRow018_meanGapNumeratorChars = some (182269 : Int) := by decide +kernel

theorem geometryRow018_meanGap_denominator_parse :
    SourceJson.intChars geometryRow018_meanGapDenominatorChars = some (264000000 : Int) := by decide +kernel

theorem geometryRow018_meanGap_denominator_nonzero : (264000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_meanGap_parse :
    parseRational geometryRow018_meanGapText = .ok geometryRowsTyped018.meanGap :=
  original_rational_fraction_of_chars geometryRow018_meanGapNumeratorChars geometryRow018_meanGapDenominatorChars
    (182269 : Int) (264000000 : Int)
    geometryRow018_meanGap_numerator_no_slash geometryRow018_meanGap_numerator_parse
    geometryRow018_meanGap_denominator_parse geometryRow018_meanGap_denominator_nonzero

theorem geometryRow018_meanGap_read :
    rationalField geometryRowsJson018 "mean_gap" = .ok geometryRowsTyped018.meanGap :=
  original_rationalField_of_string geometryRowsJson018 "mean_gap" geometryRow018_meanGapText
    geometryRowsTyped018.meanGap geometryRow018_meanGap_field geometryRow018_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_meanGap_complete"
  err.flush

noncomputable def geometryRow018_jensenBoundNumeratorChars : List Char := ['1', '2', '9', '7', '2', '4', '5', '1', '2', '2', '0', '1', '5', '6', '0', '7', '1', '0', '9', '1', '0', '4', '1', '3', '4', '5', '7', '5', '6', '5', '2', '3', '4', '7', '1', '3', '9', '4', '3', '4', '8', '9', '8', '4', '2', '0', '2', '1', '3', '3', '5', '1', '7', '2', '5', '9', '3', '7', '3', '1', '9', '9', '3', '8', '3', '4', '5', '2', '6', '8', '3', '2', '3', '3', '8', '0', '5', '8', '1', '8', '8', '4', '3', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_jensenBoundDenominatorChars : List Char := ['3', '6', '8', '7', '4', '9', '3', '0', '1', '0', '3', '6', '3', '0', '9', '0', '7', '9', '5', '2', '0', '6', '2', '8', '3', '2', '7', '9', '9', '4', '0', '7', '9', '7', '2', '8', '7', '1', '7', '1', '4', '5', '0', '4', '4', '2', '0', '2', '5', '4', '6', '9', '1', '3', '2', '9', '2', '9', '6', '1', '3', '0', '7', '3', '4', '4', '6', '2', '0', '9', '0', '1', '5', '1', '5', '3', '4', '7', '4', '1', '7', '6', '4', '9', '6', '6', '1', '5', '8', '8', '3', '1', '0', '1', '9', '1', '8', '9', '2', '8', '8', '6', '1', '3', '3', '9', '3', '6', '2', '7', '2', '2', '1', '9', '6', '7']
noncomputable def geometryRow018_jensenBoundText : String := String.ofList (geometryRow018_jensenBoundNumeratorChars ++ '/' :: geometryRow018_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_jensenBound_before_field"
  err.flush

theorem geometryRow018_jensenBound_field :
    geometryRowsJson018.getObjVal? "jensen_bound" = .ok (.str geometryRow018_jensenBoundText) := by rfl

theorem geometryRow018_jensenBound_numerator_no_slash :
    geometryRow018_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow018_jensenBoundNumeratorChars = some (129724512201560710910413457565234713943489842021335172593731993834526832338058188431720000000000000000000 : Int) := by decide +kernel

theorem geometryRow018_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow018_jensenBoundDenominatorChars = some (36874930103630907952062832799407972871714504420254691329296130734462090151534741764966158831019189288613393627221967 : Int) := by decide +kernel

theorem geometryRow018_jensenBound_denominator_nonzero : (36874930103630907952062832799407972871714504420254691329296130734462090151534741764966158831019189288613393627221967 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_jensenBound_parse :
    parseRational geometryRow018_jensenBoundText = .ok geometryRowsTyped018.jensenBound :=
  original_rational_fraction_of_chars geometryRow018_jensenBoundNumeratorChars geometryRow018_jensenBoundDenominatorChars
    (129724512201560710910413457565234713943489842021335172593731993834526832338058188431720000000000000000000 : Int) (36874930103630907952062832799407972871714504420254691329296130734462090151534741764966158831019189288613393627221967 : Int)
    geometryRow018_jensenBound_numerator_no_slash geometryRow018_jensenBound_numerator_parse
    geometryRow018_jensenBound_denominator_parse geometryRow018_jensenBound_denominator_nonzero

theorem geometryRow018_jensenBound_read :
    rationalField geometryRowsJson018 "jensen_bound" = .ok geometryRowsTyped018.jensenBound :=
  original_rationalField_of_string geometryRowsJson018 "jensen_bound" geometryRow018_jensenBoundText
    geometryRowsTyped018.jensenBound geometryRow018_jensenBound_field geometryRow018_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_factorMaxima_before"
  err.flush

theorem geometryRow018_factorMaxima_read :
    rationalArrayField geometryRowsJson018 "factor_maxima" = .ok geometryRowsTyped018.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_gapWeightedMeans_before"
  err.flush

theorem geometryRow018_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson018 "gap_weighted_means" = .ok geometryRowsTyped018.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow018_floorChars : List Char := ['2', '7', '8', '7', '2', '1', '4', '7', '0', '2', '7', '5', '4', '6', '2', '4', '8', '8']
noncomputable def geometryRow018_floorText : String := String.ofList geometryRow018_floorChars

theorem geometryRow018_floor_text_read :
    geometryRowsJson018.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow018_floorText := by rfl

theorem geometryRow018_floor_chars_parse :
    SourceJson.intChars geometryRow018_floorChars = some (278721470275462488 : Int) := by decide +kernel

theorem geometryRow018_floor_parse :
    parseInteger geometryRow018_floorText = .ok geometryRowsTyped018.jensenFloorQ96 := by
  simp only [geometryRow018_floorText, parseInteger, String.toList_ofList, geometryRow018_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_018 :
    decodeGeometryRow geometryRowsJson018 = .ok geometryRowsTyped018 :=
  original_geometryRow_of_fields geometryRowsJson018 geometryRowsTyped018 geometryRow018_floorText
    geometryRow018_simplexId_read geometryRow018_vertexIds_read
    geometryRow018_physicalVolume_read geometryRow018_meanGap_read
    geometryRow018_factorMaxima_read geometryRow018_gapWeightedMeans_read
    geometryRow018_jensenBound_read geometryRow018_floor_text_read geometryRow018_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_018_original_decoder_complete"
  err.flush

theorem geometryRow018_shape :
    geometryRowsTyped018.simplexId = 18 ∧
    geometryRowsTyped018.vertexIds.size = 9 ∧ geometryRowsTyped018.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped018.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped018.factorMaxima.size = 10 ∧ geometryRowsTyped018.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson019 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped019 : GeometryRow :=
  { simplexId := 19,
    vertexIds := #[32, 30, 20, 6, 4, 3, 2, 1, 0],
    physicalVolume := ((677290058399497381683322763026354080263464667 : ℚ) / (22664365831973634048000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((172597078099769 : ℚ) / (38764923120000000 : ℚ)),
    factorMaxima := #[((5390597 : ℚ) / (60000000 : ℚ)), ((525 : ℚ) / (5504 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((576165536272671925729023363749 : ℚ) / (6690712463274180974759280000000 : ℚ)), ((54236212495565501019432910319 : ℚ) / (597385041363766158460650000000 : ℚ)), ((1904030252369326083489001187551 : ℚ) / (16726781158185452436898200000000 : ℚ)), ((771322222664630434133962874993 : ℚ) / (8363390579092726218449100000000 : ℚ)), ((252787519780902825439316611597 : ℚ) / (2787796859697575406149700000000 : ℚ)), ((2739601069187413228430079229 : ℚ) / (38015411723148755538405000000 : ℚ)), ((10972279349447044278892923487 : ℚ) / (304123293785190044307240000000 : ℚ)), ((5456413911842307416004636587 : ℚ) / (152061646892595022153620000000 : ℚ)), ((10679626172318970282816398863 : ℚ) / (304123293785190044307240000000 : ℚ)), ((6164517607032023982965183251 : ℚ) / (199128347121255386153550000000 : ℚ))],
    jensenBound := ((88324272576635448433182498856148101649360536515559518112704550643925959211516547362756983907298712242687573377226122788120567546526843535791868416427453211046649334131394332954127838464598428929924989182243164490208930884485482265291061101010691594972841033520507812500000 : ℚ) / (125270435430343586712853161628971359090144159323327905618217780778723479151277659209796918943371717431300459464451346815170920349495006981213727571827498016235851830378170224869128906502028714178764585862882834053494234661322850240158001346442238562918806162489010363855178328200834250813 : ℚ)),
    jensenFloorQ96 := (55861303567887 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_simplexId_before"
  err.flush

theorem geometryRow019_simplexId_read :
    geometryRowsJson019.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped019.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_vertexIds_before"
  err.flush

theorem geometryRow019_vertexIds_read :
    geometryRowsJson019.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped019.vertexIds := by decide +kernel

noncomputable def geometryRow019_physicalVolumeNumeratorChars : List Char := ['6', '7', '7', '2', '9', '0', '0', '5', '8', '3', '9', '9', '4', '9', '7', '3', '8', '1', '6', '8', '3', '3', '2', '2', '7', '6', '3', '0', '2', '6', '3', '5', '4', '0', '8', '0', '2', '6', '3', '4', '6', '4', '6', '6', '7']
noncomputable def geometryRow019_physicalVolumeDenominatorChars : List Char := ['2', '2', '6', '6', '4', '3', '6', '5', '8', '3', '1', '9', '7', '3', '6', '3', '4', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_physicalVolumeText : String := String.ofList (geometryRow019_physicalVolumeNumeratorChars ++ '/' :: geometryRow019_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_physicalVolume_before_field"
  err.flush

theorem geometryRow019_physicalVolume_field :
    geometryRowsJson019.getObjVal? "physical_volume" = .ok (.str geometryRow019_physicalVolumeText) := by rfl

theorem geometryRow019_physicalVolume_numerator_no_slash :
    geometryRow019_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow019_physicalVolumeNumeratorChars = some (677290058399497381683322763026354080263464667 : Int) := by decide +kernel

theorem geometryRow019_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow019_physicalVolumeDenominatorChars = some (22664365831973634048000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow019_physicalVolume_denominator_nonzero : (22664365831973634048000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_physicalVolume_parse :
    parseRational geometryRow019_physicalVolumeText = .ok geometryRowsTyped019.physicalVolume :=
  original_rational_fraction_of_chars geometryRow019_physicalVolumeNumeratorChars geometryRow019_physicalVolumeDenominatorChars
    (677290058399497381683322763026354080263464667 : Int) (22664365831973634048000000000000000000000000000000000000000000000000000 : Int)
    geometryRow019_physicalVolume_numerator_no_slash geometryRow019_physicalVolume_numerator_parse
    geometryRow019_physicalVolume_denominator_parse geometryRow019_physicalVolume_denominator_nonzero

theorem geometryRow019_physicalVolume_read :
    rationalField geometryRowsJson019 "physical_volume" = .ok geometryRowsTyped019.physicalVolume :=
  original_rationalField_of_string geometryRowsJson019 "physical_volume" geometryRow019_physicalVolumeText
    geometryRowsTyped019.physicalVolume geometryRow019_physicalVolume_field geometryRow019_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_physicalVolume_complete"
  err.flush

noncomputable def geometryRow019_meanGapNumeratorChars : List Char := ['1', '7', '2', '5', '9', '7', '0', '7', '8', '0', '9', '9', '7', '6', '9']
noncomputable def geometryRow019_meanGapDenominatorChars : List Char := ['3', '8', '7', '6', '4', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_meanGapText : String := String.ofList (geometryRow019_meanGapNumeratorChars ++ '/' :: geometryRow019_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_meanGap_before_field"
  err.flush

theorem geometryRow019_meanGap_field :
    geometryRowsJson019.getObjVal? "mean_gap" = .ok (.str geometryRow019_meanGapText) := by rfl

theorem geometryRow019_meanGap_numerator_no_slash :
    geometryRow019_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_meanGap_numerator_parse :
    SourceJson.intChars geometryRow019_meanGapNumeratorChars = some (172597078099769 : Int) := by decide +kernel

theorem geometryRow019_meanGap_denominator_parse :
    SourceJson.intChars geometryRow019_meanGapDenominatorChars = some (38764923120000000 : Int) := by decide +kernel

theorem geometryRow019_meanGap_denominator_nonzero : (38764923120000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_meanGap_parse :
    parseRational geometryRow019_meanGapText = .ok geometryRowsTyped019.meanGap :=
  original_rational_fraction_of_chars geometryRow019_meanGapNumeratorChars geometryRow019_meanGapDenominatorChars
    (172597078099769 : Int) (38764923120000000 : Int)
    geometryRow019_meanGap_numerator_no_slash geometryRow019_meanGap_numerator_parse
    geometryRow019_meanGap_denominator_parse geometryRow019_meanGap_denominator_nonzero

theorem geometryRow019_meanGap_read :
    rationalField geometryRowsJson019 "mean_gap" = .ok geometryRowsTyped019.meanGap :=
  original_rationalField_of_string geometryRowsJson019 "mean_gap" geometryRow019_meanGapText
    geometryRowsTyped019.meanGap geometryRow019_meanGap_field geometryRow019_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_meanGap_complete"
  err.flush

noncomputable def geometryRow019_jensenBoundNumeratorChars : List Char := ['8', '8', '3', '2', '4', '2', '7', '2', '5', '7', '6', '6', '3', '5', '4', '4', '8', '4', '3', '3', '1', '8', '2', '4', '9', '8', '8', '5', '6', '1', '4', '8', '1', '0', '1', '6', '4', '9', '3', '6', '0', '5', '3', '6', '5', '1', '5', '5', '5', '9', '5', '1', '8', '1', '1', '2', '7', '0', '4', '5', '5', '0', '6', '4', '3', '9', '2', '5', '9', '5', '9', '2', '1', '1', '5', '1', '6', '5', '4', '7', '3', '6', '2', '7', '5', '6', '9', '8', '3', '9', '0', '7', '2', '9', '8', '7', '1', '2', '2', '4', '2', '6', '8', '7', '5', '7', '3', '3', '7', '7', '2', '2', '6', '1', '2', '2', '7', '8', '8', '1', '2', '0', '5', '6', '7', '5', '4', '6', '5', '2', '6', '8', '4', '3', '5', '3', '5', '7', '9', '1', '8', '6', '8', '4', '1', '6', '4', '2', '7', '4', '5', '3', '2', '1', '1', '0', '4', '6', '6', '4', '9', '3', '3', '4', '1', '3', '1', '3', '9', '4', '3', '3', '2', '9', '5', '4', '1', '2', '7', '8', '3', '8', '4', '6', '4', '5', '9', '8', '4', '2', '8', '9', '2', '9', '9', '2', '4', '9', '8', '9', '1', '8', '2', '2', '4', '3', '1', '6', '4', '4', '9', '0', '2', '0', '8', '9', '3', '0', '8', '8', '4', '4', '8', '5', '4', '8', '2', '2', '6', '5', '2', '9', '1', '0', '6', '1', '1', '0', '1', '0', '1', '0', '6', '9', '1', '5', '9', '4', '9', '7', '2', '8', '4', '1', '0', '3', '3', '5', '2', '0', '5', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_jensenBoundDenominatorChars : List Char := ['1', '2', '5', '2', '7', '0', '4', '3', '5', '4', '3', '0', '3', '4', '3', '5', '8', '6', '7', '1', '2', '8', '5', '3', '1', '6', '1', '6', '2', '8', '9', '7', '1', '3', '5', '9', '0', '9', '0', '1', '4', '4', '1', '5', '9', '3', '2', '3', '3', '2', '7', '9', '0', '5', '6', '1', '8', '2', '1', '7', '7', '8', '0', '7', '7', '8', '7', '2', '3', '4', '7', '9', '1', '5', '1', '2', '7', '7', '6', '5', '9', '2', '0', '9', '7', '9', '6', '9', '1', '8', '9', '4', '3', '3', '7', '1', '7', '1', '7', '4', '3', '1', '3', '0', '0', '4', '5', '9', '4', '6', '4', '4', '5', '1', '3', '4', '6', '8', '1', '5', '1', '7', '0', '9', '2', '0', '3', '4', '9', '4', '9', '5', '0', '0', '6', '9', '8', '1', '2', '1', '3', '7', '2', '7', '5', '7', '1', '8', '2', '7', '4', '9', '8', '0', '1', '6', '2', '3', '5', '8', '5', '1', '8', '3', '0', '3', '7', '8', '1', '7', '0', '2', '2', '4', '8', '6', '9', '1', '2', '8', '9', '0', '6', '5', '0', '2', '0', '2', '8', '7', '1', '4', '1', '7', '8', '7', '6', '4', '5', '8', '5', '8', '6', '2', '8', '8', '2', '8', '3', '4', '0', '5', '3', '4', '9', '4', '2', '3', '4', '6', '6', '1', '3', '2', '2', '8', '5', '0', '2', '4', '0', '1', '5', '8', '0', '0', '1', '3', '4', '6', '4', '4', '2', '2', '3', '8', '5', '6', '2', '9', '1', '8', '8', '0', '6', '1', '6', '2', '4', '8', '9', '0', '1', '0', '3', '6', '3', '8', '5', '5', '1', '7', '8', '3', '2', '8', '2', '0', '0', '8', '3', '4', '2', '5', '0', '8', '1', '3']
noncomputable def geometryRow019_jensenBoundText : String := String.ofList (geometryRow019_jensenBoundNumeratorChars ++ '/' :: geometryRow019_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_jensenBound_before_field"
  err.flush

theorem geometryRow019_jensenBound_field :
    geometryRowsJson019.getObjVal? "jensen_bound" = .ok (.str geometryRow019_jensenBoundText) := by rfl

theorem geometryRow019_jensenBound_numerator_no_slash :
    geometryRow019_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow019_jensenBoundNumeratorChars = some (88324272576635448433182498856148101649360536515559518112704550643925959211516547362756983907298712242687573377226122788120567546526843535791868416427453211046649334131394332954127838464598428929924989182243164490208930884485482265291061101010691594972841033520507812500000 : Int) := by decide +kernel

theorem geometryRow019_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow019_jensenBoundDenominatorChars = some (125270435430343586712853161628971359090144159323327905618217780778723479151277659209796918943371717431300459464451346815170920349495006981213727571827498016235851830378170224869128906502028714178764585862882834053494234661322850240158001346442238562918806162489010363855178328200834250813 : Int) := by decide +kernel

theorem geometryRow019_jensenBound_denominator_nonzero : (125270435430343586712853161628971359090144159323327905618217780778723479151277659209796918943371717431300459464451346815170920349495006981213727571827498016235851830378170224869128906502028714178764585862882834053494234661322850240158001346442238562918806162489010363855178328200834250813 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_jensenBound_parse :
    parseRational geometryRow019_jensenBoundText = .ok geometryRowsTyped019.jensenBound :=
  original_rational_fraction_of_chars geometryRow019_jensenBoundNumeratorChars geometryRow019_jensenBoundDenominatorChars
    (88324272576635448433182498856148101649360536515559518112704550643925959211516547362756983907298712242687573377226122788120567546526843535791868416427453211046649334131394332954127838464598428929924989182243164490208930884485482265291061101010691594972841033520507812500000 : Int) (125270435430343586712853161628971359090144159323327905618217780778723479151277659209796918943371717431300459464451346815170920349495006981213727571827498016235851830378170224869128906502028714178764585862882834053494234661322850240158001346442238562918806162489010363855178328200834250813 : Int)
    geometryRow019_jensenBound_numerator_no_slash geometryRow019_jensenBound_numerator_parse
    geometryRow019_jensenBound_denominator_parse geometryRow019_jensenBound_denominator_nonzero

theorem geometryRow019_jensenBound_read :
    rationalField geometryRowsJson019 "jensen_bound" = .ok geometryRowsTyped019.jensenBound :=
  original_rationalField_of_string geometryRowsJson019 "jensen_bound" geometryRow019_jensenBoundText
    geometryRowsTyped019.jensenBound geometryRow019_jensenBound_field geometryRow019_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_factorMaxima_before"
  err.flush

theorem geometryRow019_factorMaxima_read :
    rationalArrayField geometryRowsJson019 "factor_maxima" = .ok geometryRowsTyped019.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_gapWeightedMeans_before"
  err.flush

theorem geometryRow019_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson019 "gap_weighted_means" = .ok geometryRowsTyped019.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow019_floorChars : List Char := ['5', '5', '8', '6', '1', '3', '0', '3', '5', '6', '7', '8', '8', '7']
noncomputable def geometryRow019_floorText : String := String.ofList geometryRow019_floorChars

theorem geometryRow019_floor_text_read :
    geometryRowsJson019.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow019_floorText := by rfl

theorem geometryRow019_floor_chars_parse :
    SourceJson.intChars geometryRow019_floorChars = some (55861303567887 : Int) := by decide +kernel

theorem geometryRow019_floor_parse :
    parseInteger geometryRow019_floorText = .ok geometryRowsTyped019.jensenFloorQ96 := by
  simp only [geometryRow019_floorText, parseInteger, String.toList_ofList, geometryRow019_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_019 :
    decodeGeometryRow geometryRowsJson019 = .ok geometryRowsTyped019 :=
  original_geometryRow_of_fields geometryRowsJson019 geometryRowsTyped019 geometryRow019_floorText
    geometryRow019_simplexId_read geometryRow019_vertexIds_read
    geometryRow019_physicalVolume_read geometryRow019_meanGap_read
    geometryRow019_factorMaxima_read geometryRow019_gapWeightedMeans_read
    geometryRow019_jensenBound_read geometryRow019_floor_text_read geometryRow019_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_019_original_decoder_complete"
  err.flush

theorem geometryRow019_shape :
    geometryRowsTyped019.simplexId = 19 ∧
    geometryRowsTyped019.vertexIds.size = 9 ∧ geometryRowsTyped019.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped019.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped019.factorMaxima.size = 10 ∧ geometryRowsTyped019.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson020 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped020 : GeometryRow :=
  { simplexId := 20,
    vertexIds := #[32, 30, 20, 16, 4, 3, 2, 1, 0],
    physicalVolume := ((519918621879273756423883273416918918715654003 : ℚ) / (1346397970216255488000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((474804774133 : ℚ) / (127937040000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((1286441 : ℚ) / (16000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((160006520250453667279331 : ℚ) / (1822353521413337589600000 : ℚ)), ((11950787497390302148484569 : ℚ) / (130168108672381256400000000 : ℚ)), ((208475222027468953717303183 : ℚ) / (1822353521413337589600000000 : ℚ)), ((166052119218605354540502673 : ℚ) / (1822353521413337589600000000 : ℚ)), ((18155665848603487584336749 : ℚ) / (202483724601481954400000000 : ℚ)), ((482624390657701906154287 : ℚ) / (6626740077866682144000000 : ℚ)), ((594621435956509078751147 : ℚ) / (16566850194666705360000000 : ℚ)), ((118258054347474461910613 : ℚ) / (3313370038933341072000000 : ℚ)), ((578478355297776287290187 : ℚ) / (16566850194666705360000000 : ℚ)), ((1357994212903036939306801 : ℚ) / (43389369557460418800000000 : ℚ))],
    jensenBound := ((239092750751076984788497398723210139007376345651431833538928487248095853903430393107974055618930621593949082408260744415429011789979652889404754698239614312947724795984703663109437921215977314949117714613862497136926720000000000000 : ℚ) / (32041352755570915874744166001066318197875301752860030223529171973456340031256737903527253924679555387391017509527180969843385985794123489165280001800073641827392733970138546467692108474296582483494048275856332624224867326009572351715522504498691 : ℚ)),
    jensenFloorQ96 := (591200985083106 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_simplexId_before"
  err.flush

theorem geometryRow020_simplexId_read :
    geometryRowsJson020.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped020.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_vertexIds_before"
  err.flush

theorem geometryRow020_vertexIds_read :
    geometryRowsJson020.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped020.vertexIds := by decide +kernel

noncomputable def geometryRow020_physicalVolumeNumeratorChars : List Char := ['5', '1', '9', '9', '1', '8', '6', '2', '1', '8', '7', '9', '2', '7', '3', '7', '5', '6', '4', '2', '3', '8', '8', '3', '2', '7', '3', '4', '1', '6', '9', '1', '8', '9', '1', '8', '7', '1', '5', '6', '5', '4', '0', '0', '3']
noncomputable def geometryRow020_physicalVolumeDenominatorChars : List Char := ['1', '3', '4', '6', '3', '9', '7', '9', '7', '0', '2', '1', '6', '2', '5', '5', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_physicalVolumeText : String := String.ofList (geometryRow020_physicalVolumeNumeratorChars ++ '/' :: geometryRow020_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_physicalVolume_before_field"
  err.flush

theorem geometryRow020_physicalVolume_field :
    geometryRowsJson020.getObjVal? "physical_volume" = .ok (.str geometryRow020_physicalVolumeText) := by rfl

theorem geometryRow020_physicalVolume_numerator_no_slash :
    geometryRow020_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow020_physicalVolumeNumeratorChars = some (519918621879273756423883273416918918715654003 : Int) := by decide +kernel

theorem geometryRow020_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow020_physicalVolumeDenominatorChars = some (1346397970216255488000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow020_physicalVolume_denominator_nonzero : (1346397970216255488000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_physicalVolume_parse :
    parseRational geometryRow020_physicalVolumeText = .ok geometryRowsTyped020.physicalVolume :=
  original_rational_fraction_of_chars geometryRow020_physicalVolumeNumeratorChars geometryRow020_physicalVolumeDenominatorChars
    (519918621879273756423883273416918918715654003 : Int) (1346397970216255488000000000000000000000000000000000000000000000000000 : Int)
    geometryRow020_physicalVolume_numerator_no_slash geometryRow020_physicalVolume_numerator_parse
    geometryRow020_physicalVolume_denominator_parse geometryRow020_physicalVolume_denominator_nonzero

theorem geometryRow020_physicalVolume_read :
    rationalField geometryRowsJson020 "physical_volume" = .ok geometryRowsTyped020.physicalVolume :=
  original_rationalField_of_string geometryRowsJson020 "physical_volume" geometryRow020_physicalVolumeText
    geometryRowsTyped020.physicalVolume geometryRow020_physicalVolume_field geometryRow020_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_physicalVolume_complete"
  err.flush

noncomputable def geometryRow020_meanGapNumeratorChars : List Char := ['4', '7', '4', '8', '0', '4', '7', '7', '4', '1', '3', '3']
noncomputable def geometryRow020_meanGapDenominatorChars : List Char := ['1', '2', '7', '9', '3', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_meanGapText : String := String.ofList (geometryRow020_meanGapNumeratorChars ++ '/' :: geometryRow020_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_meanGap_before_field"
  err.flush

theorem geometryRow020_meanGap_field :
    geometryRowsJson020.getObjVal? "mean_gap" = .ok (.str geometryRow020_meanGapText) := by rfl

theorem geometryRow020_meanGap_numerator_no_slash :
    geometryRow020_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_meanGap_numerator_parse :
    SourceJson.intChars geometryRow020_meanGapNumeratorChars = some (474804774133 : Int) := by decide +kernel

theorem geometryRow020_meanGap_denominator_parse :
    SourceJson.intChars geometryRow020_meanGapDenominatorChars = some (127937040000000 : Int) := by decide +kernel

theorem geometryRow020_meanGap_denominator_nonzero : (127937040000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_meanGap_parse :
    parseRational geometryRow020_meanGapText = .ok geometryRowsTyped020.meanGap :=
  original_rational_fraction_of_chars geometryRow020_meanGapNumeratorChars geometryRow020_meanGapDenominatorChars
    (474804774133 : Int) (127937040000000 : Int)
    geometryRow020_meanGap_numerator_no_slash geometryRow020_meanGap_numerator_parse
    geometryRow020_meanGap_denominator_parse geometryRow020_meanGap_denominator_nonzero

theorem geometryRow020_meanGap_read :
    rationalField geometryRowsJson020 "mean_gap" = .ok geometryRowsTyped020.meanGap :=
  original_rationalField_of_string geometryRowsJson020 "mean_gap" geometryRow020_meanGapText
    geometryRowsTyped020.meanGap geometryRow020_meanGap_field geometryRow020_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_meanGap_complete"
  err.flush

noncomputable def geometryRow020_jensenBoundNumeratorChars : List Char := ['2', '3', '9', '0', '9', '2', '7', '5', '0', '7', '5', '1', '0', '7', '6', '9', '8', '4', '7', '8', '8', '4', '9', '7', '3', '9', '8', '7', '2', '3', '2', '1', '0', '1', '3', '9', '0', '0', '7', '3', '7', '6', '3', '4', '5', '6', '5', '1', '4', '3', '1', '8', '3', '3', '5', '3', '8', '9', '2', '8', '4', '8', '7', '2', '4', '8', '0', '9', '5', '8', '5', '3', '9', '0', '3', '4', '3', '0', '3', '9', '3', '1', '0', '7', '9', '7', '4', '0', '5', '5', '6', '1', '8', '9', '3', '0', '6', '2', '1', '5', '9', '3', '9', '4', '9', '0', '8', '2', '4', '0', '8', '2', '6', '0', '7', '4', '4', '4', '1', '5', '4', '2', '9', '0', '1', '1', '7', '8', '9', '9', '7', '9', '6', '5', '2', '8', '8', '9', '4', '0', '4', '7', '5', '4', '6', '9', '8', '2', '3', '9', '6', '1', '4', '3', '1', '2', '9', '4', '7', '7', '2', '4', '7', '9', '5', '9', '8', '4', '7', '0', '3', '6', '6', '3', '1', '0', '9', '4', '3', '7', '9', '2', '1', '2', '1', '5', '9', '7', '7', '3', '1', '4', '9', '4', '9', '1', '1', '7', '7', '1', '4', '6', '1', '3', '8', '6', '2', '4', '9', '7', '1', '3', '6', '9', '2', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_jensenBoundDenominatorChars : List Char := ['3', '2', '0', '4', '1', '3', '5', '2', '7', '5', '5', '5', '7', '0', '9', '1', '5', '8', '7', '4', '7', '4', '4', '1', '6', '6', '0', '0', '1', '0', '6', '6', '3', '1', '8', '1', '9', '7', '8', '7', '5', '3', '0', '1', '7', '5', '2', '8', '6', '0', '0', '3', '0', '2', '2', '3', '5', '2', '9', '1', '7', '1', '9', '7', '3', '4', '5', '6', '3', '4', '0', '0', '3', '1', '2', '5', '6', '7', '3', '7', '9', '0', '3', '5', '2', '7', '2', '5', '3', '9', '2', '4', '6', '7', '9', '5', '5', '5', '3', '8', '7', '3', '9', '1', '0', '1', '7', '5', '0', '9', '5', '2', '7', '1', '8', '0', '9', '6', '9', '8', '4', '3', '3', '8', '5', '9', '8', '5', '7', '9', '4', '1', '2', '3', '4', '8', '9', '1', '6', '5', '2', '8', '0', '0', '0', '1', '8', '0', '0', '0', '7', '3', '6', '4', '1', '8', '2', '7', '3', '9', '2', '7', '3', '3', '9', '7', '0', '1', '3', '8', '5', '4', '6', '4', '6', '7', '6', '9', '2', '1', '0', '8', '4', '7', '4', '2', '9', '6', '5', '8', '2', '4', '8', '3', '4', '9', '4', '0', '4', '8', '2', '7', '5', '8', '5', '6', '3', '3', '2', '6', '2', '4', '2', '2', '4', '8', '6', '7', '3', '2', '6', '0', '0', '9', '5', '7', '2', '3', '5', '1', '7', '1', '5', '5', '2', '2', '5', '0', '4', '4', '9', '8', '6', '9', '1']
noncomputable def geometryRow020_jensenBoundText : String := String.ofList (geometryRow020_jensenBoundNumeratorChars ++ '/' :: geometryRow020_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_jensenBound_before_field"
  err.flush

theorem geometryRow020_jensenBound_field :
    geometryRowsJson020.getObjVal? "jensen_bound" = .ok (.str geometryRow020_jensenBoundText) := by rfl

theorem geometryRow020_jensenBound_numerator_no_slash :
    geometryRow020_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow020_jensenBoundNumeratorChars = some (239092750751076984788497398723210139007376345651431833538928487248095853903430393107974055618930621593949082408260744415429011789979652889404754698239614312947724795984703663109437921215977314949117714613862497136926720000000000000 : Int) := by decide +kernel

theorem geometryRow020_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow020_jensenBoundDenominatorChars = some (32041352755570915874744166001066318197875301752860030223529171973456340031256737903527253924679555387391017509527180969843385985794123489165280001800073641827392733970138546467692108474296582483494048275856332624224867326009572351715522504498691 : Int) := by decide +kernel

theorem geometryRow020_jensenBound_denominator_nonzero : (32041352755570915874744166001066318197875301752860030223529171973456340031256737903527253924679555387391017509527180969843385985794123489165280001800073641827392733970138546467692108474296582483494048275856332624224867326009572351715522504498691 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_jensenBound_parse :
    parseRational geometryRow020_jensenBoundText = .ok geometryRowsTyped020.jensenBound :=
  original_rational_fraction_of_chars geometryRow020_jensenBoundNumeratorChars geometryRow020_jensenBoundDenominatorChars
    (239092750751076984788497398723210139007376345651431833538928487248095853903430393107974055618930621593949082408260744415429011789979652889404754698239614312947724795984703663109437921215977314949117714613862497136926720000000000000 : Int) (32041352755570915874744166001066318197875301752860030223529171973456340031256737903527253924679555387391017509527180969843385985794123489165280001800073641827392733970138546467692108474296582483494048275856332624224867326009572351715522504498691 : Int)
    geometryRow020_jensenBound_numerator_no_slash geometryRow020_jensenBound_numerator_parse
    geometryRow020_jensenBound_denominator_parse geometryRow020_jensenBound_denominator_nonzero

theorem geometryRow020_jensenBound_read :
    rationalField geometryRowsJson020 "jensen_bound" = .ok geometryRowsTyped020.jensenBound :=
  original_rationalField_of_string geometryRowsJson020 "jensen_bound" geometryRow020_jensenBoundText
    geometryRowsTyped020.jensenBound geometryRow020_jensenBound_field geometryRow020_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_factorMaxima_before"
  err.flush

theorem geometryRow020_factorMaxima_read :
    rationalArrayField geometryRowsJson020 "factor_maxima" = .ok geometryRowsTyped020.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_gapWeightedMeans_before"
  err.flush

theorem geometryRow020_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson020 "gap_weighted_means" = .ok geometryRowsTyped020.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow020_floorChars : List Char := ['5', '9', '1', '2', '0', '0', '9', '8', '5', '0', '8', '3', '1', '0', '6']
noncomputable def geometryRow020_floorText : String := String.ofList geometryRow020_floorChars

theorem geometryRow020_floor_text_read :
    geometryRowsJson020.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow020_floorText := by rfl

theorem geometryRow020_floor_chars_parse :
    SourceJson.intChars geometryRow020_floorChars = some (591200985083106 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_020_original_decoder_complete"
  err.flush

theorem geometryRow020_shape :
    geometryRowsTyped020.simplexId = 20 ∧
    geometryRowsTyped020.vertexIds.size = 9 ∧ geometryRowsTyped020.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped020.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped020.factorMaxima.size = 10 ∧ geometryRowsTyped020.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson021 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped021 : GeometryRow :=
  { simplexId := 21,
    vertexIds := #[32, 30, 20, 16, 15, 4, 2, 1, 0],
    physicalVolume := ((950207185734600557377465403772895399301 : ℚ) / (7045105658108313600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1133902280579 : ℚ) / (383811120000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((7769586827126251946982077 : ℚ) / (87040860855916047696000000 : ℚ)), ((334671332440020059164777 : ℚ) / (3614653690029736200000000 : ℚ)), ((41701719319237208676140167 : ℚ) / (362670253566316865400000000 : ℚ)), ((98005616521602039922805731 : ℚ) / (1088010760698950596200000000 : ℚ)), ((48211399180620123214461301 : ℚ) / (544005380349475298100000000 : ℚ)), ((6067300685463587767699 : ℚ) / (82425057628708378500000 : ℚ)), ((141301604644940714843753 : ℚ) / (3956402766178002168000000 : ℚ)), ((351180101466595650304091 : ℚ) / (9891006915445005420000000 : ℚ)), ((345803866159894464227627 : ℚ) / (9891006915445005420000000 : ℚ)), ((114067072785271631061299 : ℚ) / (3614653690029736200000000 : ℚ))],
    jensenBound := ((11568972832523281093032711821603895186851448349192397990796467398732591611608449252058129523890442339048205391325959050976240294017402899157168329227510705539432309519583848373488852353595247657296225261073531250000000000 : ℚ) / (5670665502269814498615426462126396817587783240025418296132210365822401591109643507384349311634483535254343047726558384045574053111012348095402535790318312528046637417509138801226196969660754219586762778747750440955084587447890067222452741 : ℚ)),
    jensenFloorQ96 := (161636841272 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_simplexId_before"
  err.flush

theorem geometryRow021_simplexId_read :
    geometryRowsJson021.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped021.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_vertexIds_before"
  err.flush

theorem geometryRow021_vertexIds_read :
    geometryRowsJson021.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped021.vertexIds := by decide +kernel

noncomputable def geometryRow021_physicalVolumeNumeratorChars : List Char := ['9', '5', '0', '2', '0', '7', '1', '8', '5', '7', '3', '4', '6', '0', '0', '5', '5', '7', '3', '7', '7', '4', '6', '5', '4', '0', '3', '7', '7', '2', '8', '9', '5', '3', '9', '9', '3', '0', '1']
noncomputable def geometryRow021_physicalVolumeDenominatorChars : List Char := ['7', '0', '4', '5', '1', '0', '5', '6', '5', '8', '1', '0', '8', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow021_physicalVolumeText : String := String.ofList (geometryRow021_physicalVolumeNumeratorChars ++ '/' :: geometryRow021_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_physicalVolume_before_field"
  err.flush

theorem geometryRow021_physicalVolume_field :
    geometryRowsJson021.getObjVal? "physical_volume" = .ok (.str geometryRow021_physicalVolumeText) := by rfl

theorem geometryRow021_physicalVolume_numerator_no_slash :
    geometryRow021_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow021_physicalVolumeNumeratorChars = some (950207185734600557377465403772895399301 : Int) := by decide +kernel

theorem geometryRow021_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow021_physicalVolumeDenominatorChars = some (7045105658108313600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow021_physicalVolume_denominator_nonzero : (7045105658108313600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_physicalVolume_parse :
    parseRational geometryRow021_physicalVolumeText = .ok geometryRowsTyped021.physicalVolume :=
  original_rational_fraction_of_chars geometryRow021_physicalVolumeNumeratorChars geometryRow021_physicalVolumeDenominatorChars
    (950207185734600557377465403772895399301 : Int) (7045105658108313600000000000000000000000000000000000000000000000000 : Int)
    geometryRow021_physicalVolume_numerator_no_slash geometryRow021_physicalVolume_numerator_parse
    geometryRow021_physicalVolume_denominator_parse geometryRow021_physicalVolume_denominator_nonzero

theorem geometryRow021_physicalVolume_read :
    rationalField geometryRowsJson021 "physical_volume" = .ok geometryRowsTyped021.physicalVolume :=
  original_rationalField_of_string geometryRowsJson021 "physical_volume" geometryRow021_physicalVolumeText
    geometryRowsTyped021.physicalVolume geometryRow021_physicalVolume_field geometryRow021_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_physicalVolume_complete"
  err.flush

noncomputable def geometryRow021_meanGapNumeratorChars : List Char := ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9']
noncomputable def geometryRow021_meanGapDenominatorChars : List Char := ['3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow021_meanGapText : String := String.ofList (geometryRow021_meanGapNumeratorChars ++ '/' :: geometryRow021_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_meanGap_before_field"
  err.flush

theorem geometryRow021_meanGap_field :
    geometryRowsJson021.getObjVal? "mean_gap" = .ok (.str geometryRow021_meanGapText) := by rfl

theorem geometryRow021_meanGap_numerator_no_slash :
    geometryRow021_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_meanGap_numerator_parse :
    SourceJson.intChars geometryRow021_meanGapNumeratorChars = some (1133902280579 : Int) := by decide +kernel

theorem geometryRow021_meanGap_denominator_parse :
    SourceJson.intChars geometryRow021_meanGapDenominatorChars = some (383811120000000 : Int) := by decide +kernel

theorem geometryRow021_meanGap_denominator_nonzero : (383811120000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_meanGap_parse :
    parseRational geometryRow021_meanGapText = .ok geometryRowsTyped021.meanGap :=
  original_rational_fraction_of_chars geometryRow021_meanGapNumeratorChars geometryRow021_meanGapDenominatorChars
    (1133902280579 : Int) (383811120000000 : Int)
    geometryRow021_meanGap_numerator_no_slash geometryRow021_meanGap_numerator_parse
    geometryRow021_meanGap_denominator_parse geometryRow021_meanGap_denominator_nonzero

theorem geometryRow021_meanGap_read :
    rationalField geometryRowsJson021 "mean_gap" = .ok geometryRowsTyped021.meanGap :=
  original_rationalField_of_string geometryRowsJson021 "mean_gap" geometryRow021_meanGapText
    geometryRowsTyped021.meanGap geometryRow021_meanGap_field geometryRow021_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_meanGap_complete"
  err.flush

noncomputable def geometryRow021_jensenBoundNumeratorChars : List Char := ['1', '1', '5', '6', '8', '9', '7', '2', '8', '3', '2', '5', '2', '3', '2', '8', '1', '0', '9', '3', '0', '3', '2', '7', '1', '1', '8', '2', '1', '6', '0', '3', '8', '9', '5', '1', '8', '6', '8', '5', '1', '4', '4', '8', '3', '4', '9', '1', '9', '2', '3', '9', '7', '9', '9', '0', '7', '9', '6', '4', '6', '7', '3', '9', '8', '7', '3', '2', '5', '9', '1', '6', '1', '1', '6', '0', '8', '4', '4', '9', '2', '5', '2', '0', '5', '8', '1', '2', '9', '5', '2', '3', '8', '9', '0', '4', '4', '2', '3', '3', '9', '0', '4', '8', '2', '0', '5', '3', '9', '1', '3', '2', '5', '9', '5', '9', '0', '5', '0', '9', '7', '6', '2', '4', '0', '2', '9', '4', '0', '1', '7', '4', '0', '2', '8', '9', '9', '1', '5', '7', '1', '6', '8', '3', '2', '9', '2', '2', '7', '5', '1', '0', '7', '0', '5', '5', '3', '9', '4', '3', '2', '3', '0', '9', '5', '1', '9', '5', '8', '3', '8', '4', '8', '3', '7', '3', '4', '8', '8', '8', '5', '2', '3', '5', '3', '5', '9', '5', '2', '4', '7', '6', '5', '7', '2', '9', '6', '2', '2', '5', '2', '6', '1', '0', '7', '3', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow021_jensenBoundDenominatorChars : List Char := ['5', '6', '7', '0', '6', '6', '5', '5', '0', '2', '2', '6', '9', '8', '1', '4', '4', '9', '8', '6', '1', '5', '4', '2', '6', '4', '6', '2', '1', '2', '6', '3', '9', '6', '8', '1', '7', '5', '8', '7', '7', '8', '3', '2', '4', '0', '0', '2', '5', '4', '1', '8', '2', '9', '6', '1', '3', '2', '2', '1', '0', '3', '6', '5', '8', '2', '2', '4', '0', '1', '5', '9', '1', '1', '0', '9', '6', '4', '3', '5', '0', '7', '3', '8', '4', '3', '4', '9', '3', '1', '1', '6', '3', '4', '4', '8', '3', '5', '3', '5', '2', '5', '4', '3', '4', '3', '0', '4', '7', '7', '2', '6', '5', '5', '8', '3', '8', '4', '0', '4', '5', '5', '7', '4', '0', '5', '3', '1', '1', '1', '0', '1', '2', '3', '4', '8', '0', '9', '5', '4', '0', '2', '5', '3', '5', '7', '9', '0', '3', '1', '8', '3', '1', '2', '5', '2', '8', '0', '4', '6', '6', '3', '7', '4', '1', '7', '5', '0', '9', '1', '3', '8', '8', '0', '1', '2', '2', '6', '1', '9', '6', '9', '6', '9', '6', '6', '0', '7', '5', '4', '2', '1', '9', '5', '8', '6', '7', '6', '2', '7', '7', '8', '7', '4', '7', '7', '5', '0', '4', '4', '0', '9', '5', '5', '0', '8', '4', '5', '8', '7', '4', '4', '7', '8', '9', '0', '0', '6', '7', '2', '2', '2', '4', '5', '2', '7', '4', '1']
noncomputable def geometryRow021_jensenBoundText : String := String.ofList (geometryRow021_jensenBoundNumeratorChars ++ '/' :: geometryRow021_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_jensenBound_before_field"
  err.flush

theorem geometryRow021_jensenBound_field :
    geometryRowsJson021.getObjVal? "jensen_bound" = .ok (.str geometryRow021_jensenBoundText) := by rfl

theorem geometryRow021_jensenBound_numerator_no_slash :
    geometryRow021_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow021_jensenBoundNumeratorChars = some (11568972832523281093032711821603895186851448349192397990796467398732591611608449252058129523890442339048205391325959050976240294017402899157168329227510705539432309519583848373488852353595247657296225261073531250000000000 : Int) := by decide +kernel

theorem geometryRow021_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow021_jensenBoundDenominatorChars = some (5670665502269814498615426462126396817587783240025418296132210365822401591109643507384349311634483535254343047726558384045574053111012348095402535790318312528046637417509138801226196969660754219586762778747750440955084587447890067222452741 : Int) := by decide +kernel

theorem geometryRow021_jensenBound_denominator_nonzero : (5670665502269814498615426462126396817587783240025418296132210365822401591109643507384349311634483535254343047726558384045574053111012348095402535790318312528046637417509138801226196969660754219586762778747750440955084587447890067222452741 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_jensenBound_parse :
    parseRational geometryRow021_jensenBoundText = .ok geometryRowsTyped021.jensenBound :=
  original_rational_fraction_of_chars geometryRow021_jensenBoundNumeratorChars geometryRow021_jensenBoundDenominatorChars
    (11568972832523281093032711821603895186851448349192397990796467398732591611608449252058129523890442339048205391325959050976240294017402899157168329227510705539432309519583848373488852353595247657296225261073531250000000000 : Int) (5670665502269814498615426462126396817587783240025418296132210365822401591109643507384349311634483535254343047726558384045574053111012348095402535790318312528046637417509138801226196969660754219586762778747750440955084587447890067222452741 : Int)
    geometryRow021_jensenBound_numerator_no_slash geometryRow021_jensenBound_numerator_parse
    geometryRow021_jensenBound_denominator_parse geometryRow021_jensenBound_denominator_nonzero

theorem geometryRow021_jensenBound_read :
    rationalField geometryRowsJson021 "jensen_bound" = .ok geometryRowsTyped021.jensenBound :=
  original_rationalField_of_string geometryRowsJson021 "jensen_bound" geometryRow021_jensenBoundText
    geometryRowsTyped021.jensenBound geometryRow021_jensenBound_field geometryRow021_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_factorMaxima_before"
  err.flush

theorem geometryRow021_factorMaxima_read :
    rationalArrayField geometryRowsJson021 "factor_maxima" = .ok geometryRowsTyped021.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_gapWeightedMeans_before"
  err.flush

theorem geometryRow021_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson021 "gap_weighted_means" = .ok geometryRowsTyped021.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow021_floorChars : List Char := ['1', '6', '1', '6', '3', '6', '8', '4', '1', '2', '7', '2']
noncomputable def geometryRow021_floorText : String := String.ofList geometryRow021_floorChars

theorem geometryRow021_floor_text_read :
    geometryRowsJson021.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow021_floorText := by rfl

theorem geometryRow021_floor_chars_parse :
    SourceJson.intChars geometryRow021_floorChars = some (161636841272 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_021_original_decoder_complete"
  err.flush

theorem geometryRow021_shape :
    geometryRowsTyped021.simplexId = 21 ∧
    geometryRowsTyped021.vertexIds.size = 9 ∧ geometryRowsTyped021.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped021.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped021.factorMaxima.size = 10 ∧ geometryRowsTyped021.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson022 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped022 : GeometryRow :=
  { simplexId := 22,
    vertexIds := #[32, 30, 20, 16, 15, 13, 4, 1, 0],
    physicalVolume := ((9406353106063266873759087935730430210061 : ℚ) / (7705584313555968000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((4954395717452504095483 : ℚ) / (55149676425373241250000 : ℚ)), ((1355556281884229120543 : ℚ) / (14657721309069300000000 : ℚ)), ((29542429779639312965929 : ℚ) / (255766615306078800000000 : ℚ)), ((1575544859217297178881761 : ℚ) / (17647896456119437200000000 : ℚ)), ((1549871022145147599479287 : ℚ) / (17647896456119437200000000 : ℚ)), ((7907606066650398971263 : ℚ) / (106956948218905680000000 : ℚ)), ((23063632894010467069 : ℚ) / (641741689313434080000 : ℚ)), ((5729966370028877830051 : ℚ) / (160435422328358520000000 : ℚ)), ((5642762044994955792067 : ℚ) / (160435422328358520000000 : ℚ)), ((462030198487000627741 : ℚ) / (14657721309069300000000 : ℚ))],
    jensenBound := ((1631676615704388878258735535790666058474453204431991684629672584572134021420751312100820184073949266641451949295603691163848753161365902030056098669212331208714607481885816785021990165916800000000000000 : ℚ) / (119998279134773042872632811379305273721053944618589545123632956709478035287837595021255908844251162217202551678802593252733003460462922435545608068743026976499698951275553839617191914442241881262650845293142641936694383 : ℚ)),
    jensenFloorQ96 := (1077304949803 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_simplexId_before"
  err.flush

theorem geometryRow022_simplexId_read :
    geometryRowsJson022.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped022.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_vertexIds_before"
  err.flush

theorem geometryRow022_vertexIds_read :
    geometryRowsJson022.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped022.vertexIds := by decide +kernel

noncomputable def geometryRow022_physicalVolumeNumeratorChars : List Char := ['9', '4', '0', '6', '3', '5', '3', '1', '0', '6', '0', '6', '3', '2', '6', '6', '8', '7', '3', '7', '5', '9', '0', '8', '7', '9', '3', '5', '7', '3', '0', '4', '3', '0', '2', '1', '0', '0', '6', '1']
noncomputable def geometryRow022_physicalVolumeDenominatorChars : List Char := ['7', '7', '0', '5', '5', '8', '4', '3', '1', '3', '5', '5', '5', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_physicalVolumeText : String := String.ofList (geometryRow022_physicalVolumeNumeratorChars ++ '/' :: geometryRow022_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_physicalVolume_before_field"
  err.flush

theorem geometryRow022_physicalVolume_field :
    geometryRowsJson022.getObjVal? "physical_volume" = .ok (.str geometryRow022_physicalVolumeText) := by rfl

theorem geometryRow022_physicalVolume_numerator_no_slash :
    geometryRow022_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow022_physicalVolumeNumeratorChars = some (9406353106063266873759087935730430210061 : Int) := by decide +kernel

theorem geometryRow022_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow022_physicalVolumeDenominatorChars = some (7705584313555968000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow022_physicalVolume_denominator_nonzero : (7705584313555968000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_physicalVolume_parse :
    parseRational geometryRow022_physicalVolumeText = .ok geometryRowsTyped022.physicalVolume :=
  original_rational_fraction_of_chars geometryRow022_physicalVolumeNumeratorChars geometryRow022_physicalVolumeDenominatorChars
    (9406353106063266873759087935730430210061 : Int) (7705584313555968000000000000000000000000000000000000000000000000000 : Int)
    geometryRow022_physicalVolume_numerator_no_slash geometryRow022_physicalVolume_numerator_parse
    geometryRow022_physicalVolume_denominator_parse geometryRow022_physicalVolume_denominator_nonzero

theorem geometryRow022_physicalVolume_read :
    rationalField geometryRowsJson022 "physical_volume" = .ok geometryRowsTyped022.physicalVolume :=
  original_rationalField_of_string geometryRowsJson022 "physical_volume" geometryRow022_physicalVolumeText
    geometryRowsTyped022.physicalVolume geometryRow022_physicalVolume_field geometryRow022_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_physicalVolume_complete"
  err.flush

noncomputable def geometryRow022_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow022_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_meanGapText : String := String.ofList (geometryRow022_meanGapNumeratorChars ++ '/' :: geometryRow022_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_meanGap_before_field"
  err.flush

theorem geometryRow022_meanGap_field :
    geometryRowsJson022.getObjVal? "mean_gap" = .ok (.str geometryRow022_meanGapText) := by rfl

theorem geometryRow022_meanGap_numerator_no_slash :
    geometryRow022_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_meanGap_numerator_parse :
    SourceJson.intChars geometryRow022_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow022_meanGap_denominator_parse :
    SourceJson.intChars geometryRow022_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow022_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_meanGap_parse :
    parseRational geometryRow022_meanGapText = .ok geometryRowsTyped022.meanGap :=
  original_rational_fraction_of_chars geometryRow022_meanGapNumeratorChars geometryRow022_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow022_meanGap_numerator_no_slash geometryRow022_meanGap_numerator_parse
    geometryRow022_meanGap_denominator_parse geometryRow022_meanGap_denominator_nonzero

theorem geometryRow022_meanGap_read :
    rationalField geometryRowsJson022 "mean_gap" = .ok geometryRowsTyped022.meanGap :=
  original_rationalField_of_string geometryRowsJson022 "mean_gap" geometryRow022_meanGapText
    geometryRowsTyped022.meanGap geometryRow022_meanGap_field geometryRow022_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_meanGap_complete"
  err.flush

noncomputable def geometryRow022_jensenBoundNumeratorChars : List Char := ['1', '6', '3', '1', '6', '7', '6', '6', '1', '5', '7', '0', '4', '3', '8', '8', '8', '7', '8', '2', '5', '8', '7', '3', '5', '5', '3', '5', '7', '9', '0', '6', '6', '6', '0', '5', '8', '4', '7', '4', '4', '5', '3', '2', '0', '4', '4', '3', '1', '9', '9', '1', '6', '8', '4', '6', '2', '9', '6', '7', '2', '5', '8', '4', '5', '7', '2', '1', '3', '4', '0', '2', '1', '4', '2', '0', '7', '5', '1', '3', '1', '2', '1', '0', '0', '8', '2', '0', '1', '8', '4', '0', '7', '3', '9', '4', '9', '2', '6', '6', '6', '4', '1', '4', '5', '1', '9', '4', '9', '2', '9', '5', '6', '0', '3', '6', '9', '1', '1', '6', '3', '8', '4', '8', '7', '5', '3', '1', '6', '1', '3', '6', '5', '9', '0', '2', '0', '3', '0', '0', '5', '6', '0', '9', '8', '6', '6', '9', '2', '1', '2', '3', '3', '1', '2', '0', '8', '7', '1', '4', '6', '0', '7', '4', '8', '1', '8', '8', '5', '8', '1', '6', '7', '8', '5', '0', '2', '1', '9', '9', '0', '1', '6', '5', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_jensenBoundDenominatorChars : List Char := ['1', '1', '9', '9', '9', '8', '2', '7', '9', '1', '3', '4', '7', '7', '3', '0', '4', '2', '8', '7', '2', '6', '3', '2', '8', '1', '1', '3', '7', '9', '3', '0', '5', '2', '7', '3', '7', '2', '1', '0', '5', '3', '9', '4', '4', '6', '1', '8', '5', '8', '9', '5', '4', '5', '1', '2', '3', '6', '3', '2', '9', '5', '6', '7', '0', '9', '4', '7', '8', '0', '3', '5', '2', '8', '7', '8', '3', '7', '5', '9', '5', '0', '2', '1', '2', '5', '5', '9', '0', '8', '8', '4', '4', '2', '5', '1', '1', '6', '2', '2', '1', '7', '2', '0', '2', '5', '5', '1', '6', '7', '8', '8', '0', '2', '5', '9', '3', '2', '5', '2', '7', '3', '3', '0', '0', '3', '4', '6', '0', '4', '6', '2', '9', '2', '2', '4', '3', '5', '5', '4', '5', '6', '0', '8', '0', '6', '8', '7', '4', '3', '0', '2', '6', '9', '7', '6', '4', '9', '9', '6', '9', '8', '9', '5', '1', '2', '7', '5', '5', '5', '3', '8', '3', '9', '6', '1', '7', '1', '9', '1', '9', '1', '4', '4', '4', '2', '2', '4', '1', '8', '8', '1', '2', '6', '2', '6', '5', '0', '8', '4', '5', '2', '9', '3', '1', '4', '2', '6', '4', '1', '9', '3', '6', '6', '9', '4', '3', '8', '3']
noncomputable def geometryRow022_jensenBoundText : String := String.ofList (geometryRow022_jensenBoundNumeratorChars ++ '/' :: geometryRow022_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_jensenBound_before_field"
  err.flush

theorem geometryRow022_jensenBound_field :
    geometryRowsJson022.getObjVal? "jensen_bound" = .ok (.str geometryRow022_jensenBoundText) := by rfl

theorem geometryRow022_jensenBound_numerator_no_slash :
    geometryRow022_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow022_jensenBoundNumeratorChars = some (1631676615704388878258735535790666058474453204431991684629672584572134021420751312100820184073949266641451949295603691163848753161365902030056098669212331208714607481885816785021990165916800000000000000 : Int) := by decide +kernel

theorem geometryRow022_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow022_jensenBoundDenominatorChars = some (119998279134773042872632811379305273721053944618589545123632956709478035287837595021255908844251162217202551678802593252733003460462922435545608068743026976499698951275553839617191914442241881262650845293142641936694383 : Int) := by decide +kernel

theorem geometryRow022_jensenBound_denominator_nonzero : (119998279134773042872632811379305273721053944618589545123632956709478035287837595021255908844251162217202551678802593252733003460462922435545608068743026976499698951275553839617191914442241881262650845293142641936694383 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_jensenBound_parse :
    parseRational geometryRow022_jensenBoundText = .ok geometryRowsTyped022.jensenBound :=
  original_rational_fraction_of_chars geometryRow022_jensenBoundNumeratorChars geometryRow022_jensenBoundDenominatorChars
    (1631676615704388878258735535790666058474453204431991684629672584572134021420751312100820184073949266641451949295603691163848753161365902030056098669212331208714607481885816785021990165916800000000000000 : Int) (119998279134773042872632811379305273721053944618589545123632956709478035287837595021255908844251162217202551678802593252733003460462922435545608068743026976499698951275553839617191914442241881262650845293142641936694383 : Int)
    geometryRow022_jensenBound_numerator_no_slash geometryRow022_jensenBound_numerator_parse
    geometryRow022_jensenBound_denominator_parse geometryRow022_jensenBound_denominator_nonzero

theorem geometryRow022_jensenBound_read :
    rationalField geometryRowsJson022 "jensen_bound" = .ok geometryRowsTyped022.jensenBound :=
  original_rationalField_of_string geometryRowsJson022 "jensen_bound" geometryRow022_jensenBoundText
    geometryRowsTyped022.jensenBound geometryRow022_jensenBound_field geometryRow022_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_factorMaxima_before"
  err.flush

theorem geometryRow022_factorMaxima_read :
    rationalArrayField geometryRowsJson022 "factor_maxima" = .ok geometryRowsTyped022.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_gapWeightedMeans_before"
  err.flush

theorem geometryRow022_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson022 "gap_weighted_means" = .ok geometryRowsTyped022.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow022_floorChars : List Char := ['1', '0', '7', '7', '3', '0', '4', '9', '4', '9', '8', '0', '3']
noncomputable def geometryRow022_floorText : String := String.ofList geometryRow022_floorChars

theorem geometryRow022_floor_text_read :
    geometryRowsJson022.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow022_floorText := by rfl

theorem geometryRow022_floor_chars_parse :
    SourceJson.intChars geometryRow022_floorChars = some (1077304949803 : Int) := by decide +kernel

theorem geometryRow022_floor_parse :
    parseInteger geometryRow022_floorText = .ok geometryRowsTyped022.jensenFloorQ96 := by
  simp only [geometryRow022_floorText, parseInteger, String.toList_ofList, geometryRow022_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_022 :
    decodeGeometryRow geometryRowsJson022 = .ok geometryRowsTyped022 :=
  original_geometryRow_of_fields geometryRowsJson022 geometryRowsTyped022 geometryRow022_floorText
    geometryRow022_simplexId_read geometryRow022_vertexIds_read
    geometryRow022_physicalVolume_read geometryRow022_meanGap_read
    geometryRow022_factorMaxima_read geometryRow022_gapWeightedMeans_read
    geometryRow022_jensenBound_read geometryRow022_floor_text_read geometryRow022_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_022_original_decoder_complete"
  err.flush

theorem geometryRow022_shape :
    geometryRowsTyped022.simplexId = 22 ∧
    geometryRowsTyped022.vertexIds.size = 9 ∧ geometryRowsTyped022.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped022.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped022.factorMaxima.size = 10 ∧ geometryRowsTyped022.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson023 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped023 : GeometryRow :=
  { simplexId := 23,
    vertexIds := #[32, 30, 20, 16, 15, 13, 10, 1, 0],
    physicalVolume := ((15667730010291834021034050399817664541563 : ℚ) / (1075197811193856000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((3617668344425028391 : ℚ) / (39989779603042500000 : ℚ)), ((21128259668578209421 : ℚ) / (228513026303100000000 : ℚ)), ((10749566795122436011 : ℚ) / (92729923717200000000 : ℚ)), ((565621556894800667659 : ℚ) / (6398364736486800000000 : ℚ)), ((556313332870413427553 : ℚ) / (6398364736486800000000 : ℚ)), ((2903995910766968593 : ℚ) / (38777968099920000000 : ℚ)), ((2175855299216400173 : ℚ) / (58166952149880000000 : ℚ)), ((409522309733560183 : ℚ) / (11633390429976000000 : ℚ)), ((2015995028276629619 : ℚ) / (58166952149880000000 : ℚ)), ((7201429282946108327 : ℚ) / (228513026303100000000 : ℚ))],
    jensenBound := ((33618429275118115975609188635390698484661787291431293603736988175392256955138680111927959444358545715970363825774569866158560402348439247327112268663983904480000000000000000 : ℚ) / (313313349446015487111767742937020753153673544581304686065472930524340486273065721568993173564536862099771828496015553060530439919088762107286790810101466481663652859687970017190964675149867 : ℚ)),
    jensenFloorQ96 := (8501158290232 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_simplexId_before"
  err.flush

theorem geometryRow023_simplexId_read :
    geometryRowsJson023.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped023.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_vertexIds_before"
  err.flush

theorem geometryRow023_vertexIds_read :
    geometryRowsJson023.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped023.vertexIds := by decide +kernel

noncomputable def geometryRow023_physicalVolumeNumeratorChars : List Char := ['1', '5', '6', '6', '7', '7', '3', '0', '0', '1', '0', '2', '9', '1', '8', '3', '4', '0', '2', '1', '0', '3', '4', '0', '5', '0', '3', '9', '9', '8', '1', '7', '6', '6', '4', '5', '4', '1', '5', '6', '3']
noncomputable def geometryRow023_physicalVolumeDenominatorChars : List Char := ['1', '0', '7', '5', '1', '9', '7', '8', '1', '1', '1', '9', '3', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_physicalVolumeText : String := String.ofList (geometryRow023_physicalVolumeNumeratorChars ++ '/' :: geometryRow023_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_physicalVolume_before_field"
  err.flush

theorem geometryRow023_physicalVolume_field :
    geometryRowsJson023.getObjVal? "physical_volume" = .ok (.str geometryRow023_physicalVolumeText) := by rfl

theorem geometryRow023_physicalVolume_numerator_no_slash :
    geometryRow023_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow023_physicalVolumeNumeratorChars = some (15667730010291834021034050399817664541563 : Int) := by decide +kernel

theorem geometryRow023_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow023_physicalVolumeDenominatorChars = some (1075197811193856000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow023_physicalVolume_denominator_nonzero : (1075197811193856000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_physicalVolume_parse :
    parseRational geometryRow023_physicalVolumeText = .ok geometryRowsTyped023.physicalVolume :=
  original_rational_fraction_of_chars geometryRow023_physicalVolumeNumeratorChars geometryRow023_physicalVolumeDenominatorChars
    (15667730010291834021034050399817664541563 : Int) (1075197811193856000000000000000000000000000000000000000000000000000 : Int)
    geometryRow023_physicalVolume_numerator_no_slash geometryRow023_physicalVolume_numerator_parse
    geometryRow023_physicalVolume_denominator_parse geometryRow023_physicalVolume_denominator_nonzero

theorem geometryRow023_physicalVolume_read :
    rationalField geometryRowsJson023 "physical_volume" = .ok geometryRowsTyped023.physicalVolume :=
  original_rationalField_of_string geometryRowsJson023 "physical_volume" geometryRow023_physicalVolumeText
    geometryRowsTyped023.physicalVolume geometryRow023_physicalVolume_field geometryRow023_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_physicalVolume_complete"
  err.flush

noncomputable def geometryRow023_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow023_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_meanGapText : String := String.ofList (geometryRow023_meanGapNumeratorChars ++ '/' :: geometryRow023_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_meanGap_before_field"
  err.flush

theorem geometryRow023_meanGap_field :
    geometryRowsJson023.getObjVal? "mean_gap" = .ok (.str geometryRow023_meanGapText) := by rfl

theorem geometryRow023_meanGap_numerator_no_slash :
    geometryRow023_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_meanGap_numerator_parse :
    SourceJson.intChars geometryRow023_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow023_meanGap_denominator_parse :
    SourceJson.intChars geometryRow023_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow023_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_meanGap_parse :
    parseRational geometryRow023_meanGapText = .ok geometryRowsTyped023.meanGap :=
  original_rational_fraction_of_chars geometryRow023_meanGapNumeratorChars geometryRow023_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow023_meanGap_numerator_no_slash geometryRow023_meanGap_numerator_parse
    geometryRow023_meanGap_denominator_parse geometryRow023_meanGap_denominator_nonzero

theorem geometryRow023_meanGap_read :
    rationalField geometryRowsJson023 "mean_gap" = .ok geometryRowsTyped023.meanGap :=
  original_rationalField_of_string geometryRowsJson023 "mean_gap" geometryRow023_meanGapText
    geometryRowsTyped023.meanGap geometryRow023_meanGap_field geometryRow023_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_meanGap_complete"
  err.flush

noncomputable def geometryRow023_jensenBoundNumeratorChars : List Char := ['3', '3', '6', '1', '8', '4', '2', '9', '2', '7', '5', '1', '1', '8', '1', '1', '5', '9', '7', '5', '6', '0', '9', '1', '8', '8', '6', '3', '5', '3', '9', '0', '6', '9', '8', '4', '8', '4', '6', '6', '1', '7', '8', '7', '2', '9', '1', '4', '3', '1', '2', '9', '3', '6', '0', '3', '7', '3', '6', '9', '8', '8', '1', '7', '5', '3', '9', '2', '2', '5', '6', '9', '5', '5', '1', '3', '8', '6', '8', '0', '1', '1', '1', '9', '2', '7', '9', '5', '9', '4', '4', '4', '3', '5', '8', '5', '4', '5', '7', '1', '5', '9', '7', '0', '3', '6', '3', '8', '2', '5', '7', '7', '4', '5', '6', '9', '8', '6', '6', '1', '5', '8', '5', '6', '0', '4', '0', '2', '3', '4', '8', '4', '3', '9', '2', '4', '7', '3', '2', '7', '1', '1', '2', '2', '6', '8', '6', '6', '3', '9', '8', '3', '9', '0', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_jensenBoundDenominatorChars : List Char := ['3', '1', '3', '3', '1', '3', '3', '4', '9', '4', '4', '6', '0', '1', '5', '4', '8', '7', '1', '1', '1', '7', '6', '7', '7', '4', '2', '9', '3', '7', '0', '2', '0', '7', '5', '3', '1', '5', '3', '6', '7', '3', '5', '4', '4', '5', '8', '1', '3', '0', '4', '6', '8', '6', '0', '6', '5', '4', '7', '2', '9', '3', '0', '5', '2', '4', '3', '4', '0', '4', '8', '6', '2', '7', '3', '0', '6', '5', '7', '2', '1', '5', '6', '8', '9', '9', '3', '1', '7', '3', '5', '6', '4', '5', '3', '6', '8', '6', '2', '0', '9', '9', '7', '7', '1', '8', '2', '8', '4', '9', '6', '0', '1', '5', '5', '5', '3', '0', '6', '0', '5', '3', '0', '4', '3', '9', '9', '1', '9', '0', '8', '8', '7', '6', '2', '1', '0', '7', '2', '8', '6', '7', '9', '0', '8', '1', '0', '1', '0', '1', '4', '6', '6', '4', '8', '1', '6', '6', '3', '6', '5', '2', '8', '5', '9', '6', '8', '7', '9', '7', '0', '0', '1', '7', '1', '9', '0', '9', '6', '4', '6', '7', '5', '1', '4', '9', '8', '6', '7']
noncomputable def geometryRow023_jensenBoundText : String := String.ofList (geometryRow023_jensenBoundNumeratorChars ++ '/' :: geometryRow023_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_jensenBound_before_field"
  err.flush

theorem geometryRow023_jensenBound_field :
    geometryRowsJson023.getObjVal? "jensen_bound" = .ok (.str geometryRow023_jensenBoundText) := by rfl

theorem geometryRow023_jensenBound_numerator_no_slash :
    geometryRow023_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow023_jensenBoundNumeratorChars = some (33618429275118115975609188635390698484661787291431293603736988175392256955138680111927959444358545715970363825774569866158560402348439247327112268663983904480000000000000000 : Int) := by decide +kernel

theorem geometryRow023_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow023_jensenBoundDenominatorChars = some (313313349446015487111767742937020753153673544581304686065472930524340486273065721568993173564536862099771828496015553060530439919088762107286790810101466481663652859687970017190964675149867 : Int) := by decide +kernel

theorem geometryRow023_jensenBound_denominator_nonzero : (313313349446015487111767742937020753153673544581304686065472930524340486273065721568993173564536862099771828496015553060530439919088762107286790810101466481663652859687970017190964675149867 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_jensenBound_parse :
    parseRational geometryRow023_jensenBoundText = .ok geometryRowsTyped023.jensenBound :=
  original_rational_fraction_of_chars geometryRow023_jensenBoundNumeratorChars geometryRow023_jensenBoundDenominatorChars
    (33618429275118115975609188635390698484661787291431293603736988175392256955138680111927959444358545715970363825774569866158560402348439247327112268663983904480000000000000000 : Int) (313313349446015487111767742937020753153673544581304686065472930524340486273065721568993173564536862099771828496015553060530439919088762107286790810101466481663652859687970017190964675149867 : Int)
    geometryRow023_jensenBound_numerator_no_slash geometryRow023_jensenBound_numerator_parse
    geometryRow023_jensenBound_denominator_parse geometryRow023_jensenBound_denominator_nonzero

theorem geometryRow023_jensenBound_read :
    rationalField geometryRowsJson023 "jensen_bound" = .ok geometryRowsTyped023.jensenBound :=
  original_rationalField_of_string geometryRowsJson023 "jensen_bound" geometryRow023_jensenBoundText
    geometryRowsTyped023.jensenBound geometryRow023_jensenBound_field geometryRow023_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_factorMaxima_before"
  err.flush

theorem geometryRow023_factorMaxima_read :
    rationalArrayField geometryRowsJson023 "factor_maxima" = .ok geometryRowsTyped023.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_gapWeightedMeans_before"
  err.flush

theorem geometryRow023_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson023 "gap_weighted_means" = .ok geometryRowsTyped023.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow023_floorChars : List Char := ['8', '5', '0', '1', '1', '5', '8', '2', '9', '0', '2', '3', '2']
noncomputable def geometryRow023_floorText : String := String.ofList geometryRow023_floorChars

theorem geometryRow023_floor_text_read :
    geometryRowsJson023.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow023_floorText := by rfl

theorem geometryRow023_floor_chars_parse :
    SourceJson.intChars geometryRow023_floorChars = some (8501158290232 : Int) := by decide +kernel

theorem geometryRow023_floor_parse :
    parseInteger geometryRow023_floorText = .ok geometryRowsTyped023.jensenFloorQ96 := by
  simp only [geometryRow023_floorText, parseInteger, String.toList_ofList, geometryRow023_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_023 :
    decodeGeometryRow geometryRowsJson023 = .ok geometryRowsTyped023 :=
  original_geometryRow_of_fields geometryRowsJson023 geometryRowsTyped023 geometryRow023_floorText
    geometryRow023_simplexId_read geometryRow023_vertexIds_read
    geometryRow023_physicalVolume_read geometryRow023_meanGap_read
    geometryRow023_factorMaxima_read geometryRow023_gapWeightedMeans_read
    geometryRow023_jensenBound_read geometryRow023_floor_text_read geometryRow023_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_023_original_decoder_complete"
  err.flush

theorem geometryRow023_shape :
    geometryRowsTyped023.simplexId = 23 ∧
    geometryRowsTyped023.vertexIds.size = 9 ∧ geometryRowsTyped023.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped023.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped023.factorMaxima.size = 10 ∧ geometryRowsTyped023.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock002 : List SourceJson := [geometryRowsJson016, geometryRowsJson017, geometryRowsJson018, geometryRowsJson019, geometryRowsJson020, geometryRowsJson021, geometryRowsJson022, geometryRowsJson023]
noncomputable def geometryRowsTypedBlock002 : List GeometryRow := [geometryRowsTyped016, geometryRowsTyped017, geometryRowsTyped018, geometryRowsTyped019, geometryRowsTyped020, geometryRowsTyped021, geometryRowsTyped022, geometryRowsTyped023]

theorem geometry_Rows_block_002_push_eq (acc : List SourceJson) :
    SimplicesBlock002.blockPush acc = [geometryRowsJson023, geometryRowsJson022, geometryRowsJson021, geometryRowsJson020, geometryRowsJson019, geometryRowsJson018, geometryRowsJson017, geometryRowsJson016] ++ acc := by rfl

theorem geometry_Rows_block_002_reverse (acc : List SourceJson) :
    (SimplicesBlock002.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock002 := by
  rw [geometry_Rows_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_002 :
    geometryRowsJsonBlock002.mapM decodeGeometryRow = .ok geometryRowsTypedBlock002 := by
  simp only [geometryRowsJsonBlock002, geometryRowsTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_016, decode_geometry_Rows_017, decode_geometry_Rows_018, decode_geometry_Rows_019, decode_geometry_Rows_020, decode_geometry_Rows_021, decode_geometry_Rows_022, decode_geometry_Rows_023]
  rfl

theorem geometry_Rows_block_002_length : geometryRowsTypedBlock002.length = 8 := by rfl

#print axioms geometryRow016_simplexId_read
#print axioms geometryRow016_vertexIds_read
#print axioms geometryRow016_physicalVolume_field
#print axioms geometryRow016_physicalVolume_numerator_no_slash
#print axioms geometryRow016_physicalVolume_numerator_parse
#print axioms geometryRow016_physicalVolume_denominator_parse
#print axioms geometryRow016_physicalVolume_denominator_nonzero
#print axioms geometryRow016_physicalVolume_parse
#print axioms geometryRow016_physicalVolume_read
#print axioms geometryRow016_meanGap_field
#print axioms geometryRow016_meanGap_numerator_no_slash
#print axioms geometryRow016_meanGap_numerator_parse
#print axioms geometryRow016_meanGap_denominator_parse
#print axioms geometryRow016_meanGap_denominator_nonzero
#print axioms geometryRow016_meanGap_parse
#print axioms geometryRow016_meanGap_read
#print axioms geometryRow016_jensenBound_field
#print axioms geometryRow016_jensenBound_numerator_no_slash
#print axioms geometryRow016_jensenBound_numerator_parse
#print axioms geometryRow016_jensenBound_denominator_parse
#print axioms geometryRow016_jensenBound_denominator_nonzero
#print axioms geometryRow016_jensenBound_parse
#print axioms geometryRow016_jensenBound_read
#print axioms geometryRow016_factorMaxima_read
#print axioms geometryRow016_gapWeightedMeans_read
#print axioms geometryRow016_floor_text_read
#print axioms geometryRow016_floor_chars_parse
#print axioms geometryRow016_floor_parse
#print axioms decode_geometry_Rows_016
#print axioms geometryRow016_shape
#print axioms geometryRow017_simplexId_read
#print axioms geometryRow017_vertexIds_read
#print axioms geometryRow017_physicalVolume_field
#print axioms geometryRow017_physicalVolume_numerator_no_slash
#print axioms geometryRow017_physicalVolume_numerator_parse
#print axioms geometryRow017_physicalVolume_denominator_parse
#print axioms geometryRow017_physicalVolume_denominator_nonzero
#print axioms geometryRow017_physicalVolume_parse
#print axioms geometryRow017_physicalVolume_read
#print axioms geometryRow017_meanGap_field
#print axioms geometryRow017_meanGap_numerator_no_slash
#print axioms geometryRow017_meanGap_numerator_parse
#print axioms geometryRow017_meanGap_denominator_parse
#print axioms geometryRow017_meanGap_denominator_nonzero
#print axioms geometryRow017_meanGap_parse
#print axioms geometryRow017_meanGap_read
#print axioms geometryRow017_jensenBound_field
#print axioms geometryRow017_jensenBound_numerator_no_slash
#print axioms geometryRow017_jensenBound_numerator_parse
#print axioms geometryRow017_jensenBound_denominator_parse
#print axioms geometryRow017_jensenBound_denominator_nonzero
#print axioms geometryRow017_jensenBound_parse
#print axioms geometryRow017_jensenBound_read
#print axioms geometryRow017_factorMaxima_read
#print axioms geometryRow017_gapWeightedMeans_read
#print axioms geometryRow017_floor_text_read
#print axioms geometryRow017_floor_chars_parse
#print axioms geometryRow017_floor_parse
#print axioms decode_geometry_Rows_017
#print axioms geometryRow017_shape
#print axioms geometryRow018_simplexId_read
#print axioms geometryRow018_vertexIds_read
#print axioms geometryRow018_physicalVolume_field
#print axioms geometryRow018_physicalVolume_numerator_no_slash
#print axioms geometryRow018_physicalVolume_numerator_parse
#print axioms geometryRow018_physicalVolume_denominator_parse
#print axioms geometryRow018_physicalVolume_denominator_nonzero
#print axioms geometryRow018_physicalVolume_parse
#print axioms geometryRow018_physicalVolume_read
#print axioms geometryRow018_meanGap_field
#print axioms geometryRow018_meanGap_numerator_no_slash
#print axioms geometryRow018_meanGap_numerator_parse
#print axioms geometryRow018_meanGap_denominator_parse
#print axioms geometryRow018_meanGap_denominator_nonzero
#print axioms geometryRow018_meanGap_parse
#print axioms geometryRow018_meanGap_read
#print axioms geometryRow018_jensenBound_field
#print axioms geometryRow018_jensenBound_numerator_no_slash
#print axioms geometryRow018_jensenBound_numerator_parse
#print axioms geometryRow018_jensenBound_denominator_parse
#print axioms geometryRow018_jensenBound_denominator_nonzero
#print axioms geometryRow018_jensenBound_parse
#print axioms geometryRow018_jensenBound_read
#print axioms geometryRow018_factorMaxima_read
#print axioms geometryRow018_gapWeightedMeans_read
#print axioms geometryRow018_floor_text_read
#print axioms geometryRow018_floor_chars_parse
#print axioms geometryRow018_floor_parse
#print axioms decode_geometry_Rows_018
#print axioms geometryRow018_shape
#print axioms geometryRow019_simplexId_read
#print axioms geometryRow019_vertexIds_read
#print axioms geometryRow019_physicalVolume_field
#print axioms geometryRow019_physicalVolume_numerator_no_slash
#print axioms geometryRow019_physicalVolume_numerator_parse
#print axioms geometryRow019_physicalVolume_denominator_parse
#print axioms geometryRow019_physicalVolume_denominator_nonzero
#print axioms geometryRow019_physicalVolume_parse
#print axioms geometryRow019_physicalVolume_read
#print axioms geometryRow019_meanGap_field
#print axioms geometryRow019_meanGap_numerator_no_slash
#print axioms geometryRow019_meanGap_numerator_parse
#print axioms geometryRow019_meanGap_denominator_parse
#print axioms geometryRow019_meanGap_denominator_nonzero
#print axioms geometryRow019_meanGap_parse
#print axioms geometryRow019_meanGap_read
#print axioms geometryRow019_jensenBound_field
#print axioms geometryRow019_jensenBound_numerator_no_slash
#print axioms geometryRow019_jensenBound_numerator_parse
#print axioms geometryRow019_jensenBound_denominator_parse
#print axioms geometryRow019_jensenBound_denominator_nonzero
#print axioms geometryRow019_jensenBound_parse
#print axioms geometryRow019_jensenBound_read
#print axioms geometryRow019_factorMaxima_read
#print axioms geometryRow019_gapWeightedMeans_read
#print axioms geometryRow019_floor_text_read
#print axioms geometryRow019_floor_chars_parse
#print axioms geometryRow019_floor_parse
#print axioms decode_geometry_Rows_019
#print axioms geometryRow019_shape
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
#print axioms geometryRow020_shape
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
#print axioms geometryRow021_shape
#print axioms geometryRow022_simplexId_read
#print axioms geometryRow022_vertexIds_read
#print axioms geometryRow022_physicalVolume_field
#print axioms geometryRow022_physicalVolume_numerator_no_slash
#print axioms geometryRow022_physicalVolume_numerator_parse
#print axioms geometryRow022_physicalVolume_denominator_parse
#print axioms geometryRow022_physicalVolume_denominator_nonzero
#print axioms geometryRow022_physicalVolume_parse
#print axioms geometryRow022_physicalVolume_read
#print axioms geometryRow022_meanGap_field
#print axioms geometryRow022_meanGap_numerator_no_slash
#print axioms geometryRow022_meanGap_numerator_parse
#print axioms geometryRow022_meanGap_denominator_parse
#print axioms geometryRow022_meanGap_denominator_nonzero
#print axioms geometryRow022_meanGap_parse
#print axioms geometryRow022_meanGap_read
#print axioms geometryRow022_jensenBound_field
#print axioms geometryRow022_jensenBound_numerator_no_slash
#print axioms geometryRow022_jensenBound_numerator_parse
#print axioms geometryRow022_jensenBound_denominator_parse
#print axioms geometryRow022_jensenBound_denominator_nonzero
#print axioms geometryRow022_jensenBound_parse
#print axioms geometryRow022_jensenBound_read
#print axioms geometryRow022_factorMaxima_read
#print axioms geometryRow022_gapWeightedMeans_read
#print axioms geometryRow022_floor_text_read
#print axioms geometryRow022_floor_chars_parse
#print axioms geometryRow022_floor_parse
#print axioms decode_geometry_Rows_022
#print axioms geometryRow022_shape
#print axioms geometryRow023_simplexId_read
#print axioms geometryRow023_vertexIds_read
#print axioms geometryRow023_physicalVolume_field
#print axioms geometryRow023_physicalVolume_numerator_no_slash
#print axioms geometryRow023_physicalVolume_numerator_parse
#print axioms geometryRow023_physicalVolume_denominator_parse
#print axioms geometryRow023_physicalVolume_denominator_nonzero
#print axioms geometryRow023_physicalVolume_parse
#print axioms geometryRow023_physicalVolume_read
#print axioms geometryRow023_meanGap_field
#print axioms geometryRow023_meanGap_numerator_no_slash
#print axioms geometryRow023_meanGap_numerator_parse
#print axioms geometryRow023_meanGap_denominator_parse
#print axioms geometryRow023_meanGap_denominator_nonzero
#print axioms geometryRow023_meanGap_parse
#print axioms geometryRow023_meanGap_read
#print axioms geometryRow023_jensenBound_field
#print axioms geometryRow023_jensenBound_numerator_no_slash
#print axioms geometryRow023_jensenBound_numerator_parse
#print axioms geometryRow023_jensenBound_denominator_parse
#print axioms geometryRow023_jensenBound_denominator_nonzero
#print axioms geometryRow023_jensenBound_parse
#print axioms geometryRow023_jensenBound_read
#print axioms geometryRow023_factorMaxima_read
#print axioms geometryRow023_gapWeightedMeans_read
#print axioms geometryRow023_floor_text_read
#print axioms geometryRow023_floor_chars_parse
#print axioms geometryRow023_floor_parse
#print axioms decode_geometry_Rows_023
#print axioms geometryRow023_shape
#print axioms geometry_Rows_block_002_push_eq
#print axioms geometry_Rows_block_002_reverse
#print axioms decode_geometry_Rows_block_002
#print axioms geometry_Rows_block_002_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
