import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock011

/-! Local typed certificates for original cell 06, rows 88 through 95.
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

noncomputable def geometryRowsJson088 : SourceJson :=
  (SimplicesBlock011.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped088 : GeometryRow :=
  { simplexId := 88,
    vertexIds := #[32, 30, 28, 26, 25, 24, 14, 13, 4],
    physicalVolume := ((6227643940743217388652656654285698820879 : ℚ) / (31266603016488000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((984203 : ℚ) / (1354500000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((32031 : ℚ) / (418750 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((28965661886143 : ℚ) / (333965520000000 : ℚ)), ((683778117469 : ℚ) / (7766640000000 : ℚ)), ((438406575361 : ℚ) / (3630060000000 : ℚ)), ((3463882977903 : ℚ) / (37107280000000 : ℚ)), ((10331155032493 : ℚ) / (111321840000000 : ℚ)), ((11782660430729 : ℚ) / (166982760000000 : ℚ)), ((339841889233 : ℚ) / (9541872000000 : ℚ)), ((1624672317881 : ℚ) / (47709360000000 : ℚ)), ((10599430576421 : ℚ) / (333965520000000 : ℚ)), ((233319078911 : ℚ) / (7766640000000 : ℚ))],
    jensenBound := ((19218898183326434102685912006098461864729559529933451415902802081862776266889473886336977993728000000000000000 : ℚ) / (21641864054292004039499632463343401518241946811187585828882308944915826334512545057208073577103181304399132123890135822341 : ℚ)),
    jensenFloorQ96 := (70357986945755238 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_simplexId_before"
  err.flush

theorem geometryRow088_simplexId_read :
    geometryRowsJson088.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped088.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_vertexIds_before"
  err.flush

theorem geometryRow088_vertexIds_read :
    geometryRowsJson088.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped088.vertexIds := by decide +kernel

noncomputable def geometryRow088_physicalVolumeNumeratorChars : List Char := ['6', '2', '2', '7', '6', '4', '3', '9', '4', '0', '7', '4', '3', '2', '1', '7', '3', '8', '8', '6', '5', '2', '6', '5', '6', '6', '5', '4', '2', '8', '5', '6', '9', '8', '8', '2', '0', '8', '7', '9']
noncomputable def geometryRow088_physicalVolumeDenominatorChars : List Char := ['3', '1', '2', '6', '6', '6', '0', '3', '0', '1', '6', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow088_physicalVolumeText : String := String.ofList (geometryRow088_physicalVolumeNumeratorChars ++ '/' :: geometryRow088_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_physicalVolume_before_field"
  err.flush

theorem geometryRow088_physicalVolume_field :
    geometryRowsJson088.getObjVal? "physical_volume" = .ok (.str geometryRow088_physicalVolumeText) := by rfl

theorem geometryRow088_physicalVolume_numerator_no_slash :
    geometryRow088_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow088_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow088_physicalVolumeNumeratorChars = some (6227643940743217388652656654285698820879 : Int) := by decide +kernel

theorem geometryRow088_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow088_physicalVolumeDenominatorChars = some (31266603016488000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow088_physicalVolume_denominator_nonzero : (31266603016488000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow088_physicalVolume_parse :
    parseRational geometryRow088_physicalVolumeText = .ok geometryRowsTyped088.physicalVolume :=
  original_rational_fraction_of_chars geometryRow088_physicalVolumeNumeratorChars geometryRow088_physicalVolumeDenominatorChars
    (6227643940743217388652656654285698820879 : Int) (31266603016488000000000000000000000000000000000000000000000000 : Int)
    geometryRow088_physicalVolume_numerator_no_slash geometryRow088_physicalVolume_numerator_parse
    geometryRow088_physicalVolume_denominator_parse geometryRow088_physicalVolume_denominator_nonzero

theorem geometryRow088_physicalVolume_read :
    rationalField geometryRowsJson088 "physical_volume" = .ok geometryRowsTyped088.physicalVolume :=
  original_rationalField_of_string geometryRowsJson088 "physical_volume" geometryRow088_physicalVolumeText
    geometryRowsTyped088.physicalVolume geometryRow088_physicalVolume_field geometryRow088_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_physicalVolume_complete"
  err.flush

noncomputable def geometryRow088_meanGapNumeratorChars : List Char := ['9', '8', '4', '2', '0', '3']
noncomputable def geometryRow088_meanGapDenominatorChars : List Char := ['1', '3', '5', '4', '5', '0', '0', '0', '0', '0']
noncomputable def geometryRow088_meanGapText : String := String.ofList (geometryRow088_meanGapNumeratorChars ++ '/' :: geometryRow088_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_meanGap_before_field"
  err.flush

theorem geometryRow088_meanGap_field :
    geometryRowsJson088.getObjVal? "mean_gap" = .ok (.str geometryRow088_meanGapText) := by rfl

theorem geometryRow088_meanGap_numerator_no_slash :
    geometryRow088_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow088_meanGap_numerator_parse :
    SourceJson.intChars geometryRow088_meanGapNumeratorChars = some (984203 : Int) := by decide +kernel

theorem geometryRow088_meanGap_denominator_parse :
    SourceJson.intChars geometryRow088_meanGapDenominatorChars = some (1354500000 : Int) := by decide +kernel

theorem geometryRow088_meanGap_denominator_nonzero : (1354500000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow088_meanGap_parse :
    parseRational geometryRow088_meanGapText = .ok geometryRowsTyped088.meanGap :=
  original_rational_fraction_of_chars geometryRow088_meanGapNumeratorChars geometryRow088_meanGapDenominatorChars
    (984203 : Int) (1354500000 : Int)
    geometryRow088_meanGap_numerator_no_slash geometryRow088_meanGap_numerator_parse
    geometryRow088_meanGap_denominator_parse geometryRow088_meanGap_denominator_nonzero

theorem geometryRow088_meanGap_read :
    rationalField geometryRowsJson088 "mean_gap" = .ok geometryRowsTyped088.meanGap :=
  original_rationalField_of_string geometryRowsJson088 "mean_gap" geometryRow088_meanGapText
    geometryRowsTyped088.meanGap geometryRow088_meanGap_field geometryRow088_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_meanGap_complete"
  err.flush

noncomputable def geometryRow088_jensenBoundNumeratorChars : List Char := ['1', '9', '2', '1', '8', '8', '9', '8', '1', '8', '3', '3', '2', '6', '4', '3', '4', '1', '0', '2', '6', '8', '5', '9', '1', '2', '0', '0', '6', '0', '9', '8', '4', '6', '1', '8', '6', '4', '7', '2', '9', '5', '5', '9', '5', '2', '9', '9', '3', '3', '4', '5', '1', '4', '1', '5', '9', '0', '2', '8', '0', '2', '0', '8', '1', '8', '6', '2', '7', '7', '6', '2', '6', '6', '8', '8', '9', '4', '7', '3', '8', '8', '6', '3', '3', '6', '9', '7', '7', '9', '9', '3', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow088_jensenBoundDenominatorChars : List Char := ['2', '1', '6', '4', '1', '8', '6', '4', '0', '5', '4', '2', '9', '2', '0', '0', '4', '0', '3', '9', '4', '9', '9', '6', '3', '2', '4', '6', '3', '3', '4', '3', '4', '0', '1', '5', '1', '8', '2', '4', '1', '9', '4', '6', '8', '1', '1', '1', '8', '7', '5', '8', '5', '8', '2', '8', '8', '8', '2', '3', '0', '8', '9', '4', '4', '9', '1', '5', '8', '2', '6', '3', '3', '4', '5', '1', '2', '5', '4', '5', '0', '5', '7', '2', '0', '8', '0', '7', '3', '5', '7', '7', '1', '0', '3', '1', '8', '1', '3', '0', '4', '3', '9', '9', '1', '3', '2', '1', '2', '3', '8', '9', '0', '1', '3', '5', '8', '2', '2', '3', '4', '1']
noncomputable def geometryRow088_jensenBoundText : String := String.ofList (geometryRow088_jensenBoundNumeratorChars ++ '/' :: geometryRow088_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_jensenBound_before_field"
  err.flush

theorem geometryRow088_jensenBound_field :
    geometryRowsJson088.getObjVal? "jensen_bound" = .ok (.str geometryRow088_jensenBoundText) := by rfl

theorem geometryRow088_jensenBound_numerator_no_slash :
    geometryRow088_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow088_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow088_jensenBoundNumeratorChars = some (19218898183326434102685912006098461864729559529933451415902802081862776266889473886336977993728000000000000000 : Int) := by decide +kernel

theorem geometryRow088_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow088_jensenBoundDenominatorChars = some (21641864054292004039499632463343401518241946811187585828882308944915826334512545057208073577103181304399132123890135822341 : Int) := by decide +kernel

theorem geometryRow088_jensenBound_denominator_nonzero : (21641864054292004039499632463343401518241946811187585828882308944915826334512545057208073577103181304399132123890135822341 : Int) ≠ 0 := by decide +kernel

theorem geometryRow088_jensenBound_parse :
    parseRational geometryRow088_jensenBoundText = .ok geometryRowsTyped088.jensenBound :=
  original_rational_fraction_of_chars geometryRow088_jensenBoundNumeratorChars geometryRow088_jensenBoundDenominatorChars
    (19218898183326434102685912006098461864729559529933451415902802081862776266889473886336977993728000000000000000 : Int) (21641864054292004039499632463343401518241946811187585828882308944915826334512545057208073577103181304399132123890135822341 : Int)
    geometryRow088_jensenBound_numerator_no_slash geometryRow088_jensenBound_numerator_parse
    geometryRow088_jensenBound_denominator_parse geometryRow088_jensenBound_denominator_nonzero

theorem geometryRow088_jensenBound_read :
    rationalField geometryRowsJson088 "jensen_bound" = .ok geometryRowsTyped088.jensenBound :=
  original_rationalField_of_string geometryRowsJson088 "jensen_bound" geometryRow088_jensenBoundText
    geometryRowsTyped088.jensenBound geometryRow088_jensenBound_field geometryRow088_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_factorMaxima_before"
  err.flush

theorem geometryRow088_factorMaxima_read :
    rationalArrayField geometryRowsJson088 "factor_maxima" = .ok geometryRowsTyped088.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_gapWeightedMeans_before"
  err.flush

theorem geometryRow088_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson088 "gap_weighted_means" = .ok geometryRowsTyped088.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow088_floorChars : List Char := ['7', '0', '3', '5', '7', '9', '8', '6', '9', '4', '5', '7', '5', '5', '2', '3', '8']
noncomputable def geometryRow088_floorText : String := String.ofList geometryRow088_floorChars

theorem geometryRow088_floor_text_read :
    geometryRowsJson088.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow088_floorText := by rfl

theorem geometryRow088_floor_chars_parse :
    SourceJson.intChars geometryRow088_floorChars = some (70357986945755238 : Int) := by decide +kernel

theorem geometryRow088_floor_parse :
    parseInteger geometryRow088_floorText = .ok geometryRowsTyped088.jensenFloorQ96 := by
  simp only [geometryRow088_floorText, parseInteger, String.toList_ofList, geometryRow088_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_088 :
    decodeGeometryRow geometryRowsJson088 = .ok geometryRowsTyped088 :=
  original_geometryRow_of_fields geometryRowsJson088 geometryRowsTyped088 geometryRow088_floorText
    geometryRow088_simplexId_read geometryRow088_vertexIds_read
    geometryRow088_physicalVolume_read geometryRow088_meanGap_read
    geometryRow088_factorMaxima_read geometryRow088_gapWeightedMeans_read
    geometryRow088_jensenBound_read geometryRow088_floor_text_read geometryRow088_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_088_original_decoder_complete"
  err.flush

theorem geometryRow088_shape :
    geometryRowsTyped088.simplexId = 88 ∧
    geometryRowsTyped088.vertexIds.size = 9 ∧ geometryRowsTyped088.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped088.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped088.factorMaxima.size = 10 ∧ geometryRowsTyped088.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson089 : SourceJson :=
  (SimplicesBlock011.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped089 : GeometryRow :=
  { simplexId := 89,
    vertexIds := #[32, 30, 28, 26, 25, 24, 9, 7, 3],
    physicalVolume := ((6327314126199821271045975037190020041751 : ℚ) / (706516160071680000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((2237411929 : ℚ) / (1055736000000 : ℚ)),
    factorMaxima := #[((8015629 : ℚ) / (88000000 : ℚ)), ((2140609 : ℚ) / (22000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((1609371 : ℚ) / (22000000 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((1609371 : ℚ) / (44000000 : ℚ)), ((5921703 : ℚ) / (172000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((74731080378544537859 : ℚ) / (869258805861105792000 : ℚ)), ((48089505862839341379029 : ℚ) / (543286753663191120000000 : ℚ)), ((114180770251574231270473 : ℚ) / (950751818910584460000000 : ℚ)), ((40137468540409441653911 : ℚ) / (422556363960259760000000 : ℚ)), ((119723535864684485141861 : ℚ) / (1267669091880779280000000 : ℚ)), ((26541486381051897976733 : ℚ) / (380300727564233784000000 : ℚ)), ((133980610830300336693607 : ℚ) / (3803007275642337840000000 : ℚ)), ((128039109180109718247211 : ℚ) / (3803007275642337840000000 : ℚ)), ((3320258438966594893661 : ℚ) / (108657350732638224000000 : ℚ)), ((16407085560664186844647 : ℚ) / (543286753663191120000000 : ℚ))],
    jensenBound := ((5928618859423381739840123584089677967642363786059731814323535036877585825338368161127160147901018157985483359796301132146843189992835620449652522687664399167416030338940247377309452976403369342500077568000000000 : ℚ) / (48908824704270516063947526491453173212156855503855310062969363030488896966687801714457410466852818528835234320722915263810311092306413835090323985998657609881099454162840300083856681217085306323851359112058455973819981528911 : ℚ)),
    jensenFloorQ96 := (9603861497790494 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_simplexId_before"
  err.flush

theorem geometryRow089_simplexId_read :
    geometryRowsJson089.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped089.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_vertexIds_before"
  err.flush

theorem geometryRow089_vertexIds_read :
    geometryRowsJson089.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped089.vertexIds := by decide +kernel

noncomputable def geometryRow089_physicalVolumeNumeratorChars : List Char := ['6', '3', '2', '7', '3', '1', '4', '1', '2', '6', '1', '9', '9', '8', '2', '1', '2', '7', '1', '0', '4', '5', '9', '7', '5', '0', '3', '7', '1', '9', '0', '0', '2', '0', '0', '4', '1', '7', '5', '1']
noncomputable def geometryRow089_physicalVolumeDenominatorChars : List Char := ['7', '0', '6', '5', '1', '6', '1', '6', '0', '0', '7', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow089_physicalVolumeText : String := String.ofList (geometryRow089_physicalVolumeNumeratorChars ++ '/' :: geometryRow089_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_physicalVolume_before_field"
  err.flush

theorem geometryRow089_physicalVolume_field :
    geometryRowsJson089.getObjVal? "physical_volume" = .ok (.str geometryRow089_physicalVolumeText) := by rfl

theorem geometryRow089_physicalVolume_numerator_no_slash :
    geometryRow089_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow089_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow089_physicalVolumeNumeratorChars = some (6327314126199821271045975037190020041751 : Int) := by decide +kernel

theorem geometryRow089_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow089_physicalVolumeDenominatorChars = some (706516160071680000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow089_physicalVolume_denominator_nonzero : (706516160071680000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow089_physicalVolume_parse :
    parseRational geometryRow089_physicalVolumeText = .ok geometryRowsTyped089.physicalVolume :=
  original_rational_fraction_of_chars geometryRow089_physicalVolumeNumeratorChars geometryRow089_physicalVolumeDenominatorChars
    (6327314126199821271045975037190020041751 : Int) (706516160071680000000000000000000000000000000000000000000000000 : Int)
    geometryRow089_physicalVolume_numerator_no_slash geometryRow089_physicalVolume_numerator_parse
    geometryRow089_physicalVolume_denominator_parse geometryRow089_physicalVolume_denominator_nonzero

theorem geometryRow089_physicalVolume_read :
    rationalField geometryRowsJson089 "physical_volume" = .ok geometryRowsTyped089.physicalVolume :=
  original_rationalField_of_string geometryRowsJson089 "physical_volume" geometryRow089_physicalVolumeText
    geometryRowsTyped089.physicalVolume geometryRow089_physicalVolume_field geometryRow089_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_physicalVolume_complete"
  err.flush

noncomputable def geometryRow089_meanGapNumeratorChars : List Char := ['2', '2', '3', '7', '4', '1', '1', '9', '2', '9']
noncomputable def geometryRow089_meanGapDenominatorChars : List Char := ['1', '0', '5', '5', '7', '3', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow089_meanGapText : String := String.ofList (geometryRow089_meanGapNumeratorChars ++ '/' :: geometryRow089_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_meanGap_before_field"
  err.flush

theorem geometryRow089_meanGap_field :
    geometryRowsJson089.getObjVal? "mean_gap" = .ok (.str geometryRow089_meanGapText) := by rfl

theorem geometryRow089_meanGap_numerator_no_slash :
    geometryRow089_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow089_meanGap_numerator_parse :
    SourceJson.intChars geometryRow089_meanGapNumeratorChars = some (2237411929 : Int) := by decide +kernel

theorem geometryRow089_meanGap_denominator_parse :
    SourceJson.intChars geometryRow089_meanGapDenominatorChars = some (1055736000000 : Int) := by decide +kernel

theorem geometryRow089_meanGap_denominator_nonzero : (1055736000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow089_meanGap_parse :
    parseRational geometryRow089_meanGapText = .ok geometryRowsTyped089.meanGap :=
  original_rational_fraction_of_chars geometryRow089_meanGapNumeratorChars geometryRow089_meanGapDenominatorChars
    (2237411929 : Int) (1055736000000 : Int)
    geometryRow089_meanGap_numerator_no_slash geometryRow089_meanGap_numerator_parse
    geometryRow089_meanGap_denominator_parse geometryRow089_meanGap_denominator_nonzero

theorem geometryRow089_meanGap_read :
    rationalField geometryRowsJson089 "mean_gap" = .ok geometryRowsTyped089.meanGap :=
  original_rationalField_of_string geometryRowsJson089 "mean_gap" geometryRow089_meanGapText
    geometryRowsTyped089.meanGap geometryRow089_meanGap_field geometryRow089_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_meanGap_complete"
  err.flush

noncomputable def geometryRow089_jensenBoundNumeratorChars : List Char := ['5', '9', '2', '8', '6', '1', '8', '8', '5', '9', '4', '2', '3', '3', '8', '1', '7', '3', '9', '8', '4', '0', '1', '2', '3', '5', '8', '4', '0', '8', '9', '6', '7', '7', '9', '6', '7', '6', '4', '2', '3', '6', '3', '7', '8', '6', '0', '5', '9', '7', '3', '1', '8', '1', '4', '3', '2', '3', '5', '3', '5', '0', '3', '6', '8', '7', '7', '5', '8', '5', '8', '2', '5', '3', '3', '8', '3', '6', '8', '1', '6', '1', '1', '2', '7', '1', '6', '0', '1', '4', '7', '9', '0', '1', '0', '1', '8', '1', '5', '7', '9', '8', '5', '4', '8', '3', '3', '5', '9', '7', '9', '6', '3', '0', '1', '1', '3', '2', '1', '4', '6', '8', '4', '3', '1', '8', '9', '9', '9', '2', '8', '3', '5', '6', '2', '0', '4', '4', '9', '6', '5', '2', '5', '2', '2', '6', '8', '7', '6', '6', '4', '3', '9', '9', '1', '6', '7', '4', '1', '6', '0', '3', '0', '3', '3', '8', '9', '4', '0', '2', '4', '7', '3', '7', '7', '3', '0', '9', '4', '5', '2', '9', '7', '6', '4', '0', '3', '3', '6', '9', '3', '4', '2', '5', '0', '0', '0', '7', '7', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow089_jensenBoundDenominatorChars : List Char := ['4', '8', '9', '0', '8', '8', '2', '4', '7', '0', '4', '2', '7', '0', '5', '1', '6', '0', '6', '3', '9', '4', '7', '5', '2', '6', '4', '9', '1', '4', '5', '3', '1', '7', '3', '2', '1', '2', '1', '5', '6', '8', '5', '5', '5', '0', '3', '8', '5', '5', '3', '1', '0', '0', '6', '2', '9', '6', '9', '3', '6', '3', '0', '3', '0', '4', '8', '8', '8', '9', '6', '9', '6', '6', '6', '8', '7', '8', '0', '1', '7', '1', '4', '4', '5', '7', '4', '1', '0', '4', '6', '6', '8', '5', '2', '8', '1', '8', '5', '2', '8', '8', '3', '5', '2', '3', '4', '3', '2', '0', '7', '2', '2', '9', '1', '5', '2', '6', '3', '8', '1', '0', '3', '1', '1', '0', '9', '2', '3', '0', '6', '4', '1', '3', '8', '3', '5', '0', '9', '0', '3', '2', '3', '9', '8', '5', '9', '9', '8', '6', '5', '7', '6', '0', '9', '8', '8', '1', '0', '9', '9', '4', '5', '4', '1', '6', '2', '8', '4', '0', '3', '0', '0', '0', '8', '3', '8', '5', '6', '6', '8', '1', '2', '1', '7', '0', '8', '5', '3', '0', '6', '3', '2', '3', '8', '5', '1', '3', '5', '9', '1', '1', '2', '0', '5', '8', '4', '5', '5', '9', '7', '3', '8', '1', '9', '9', '8', '1', '5', '2', '8', '9', '1', '1']
noncomputable def geometryRow089_jensenBoundText : String := String.ofList (geometryRow089_jensenBoundNumeratorChars ++ '/' :: geometryRow089_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_jensenBound_before_field"
  err.flush

theorem geometryRow089_jensenBound_field :
    geometryRowsJson089.getObjVal? "jensen_bound" = .ok (.str geometryRow089_jensenBoundText) := by rfl

theorem geometryRow089_jensenBound_numerator_no_slash :
    geometryRow089_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow089_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow089_jensenBoundNumeratorChars = some (5928618859423381739840123584089677967642363786059731814323535036877585825338368161127160147901018157985483359796301132146843189992835620449652522687664399167416030338940247377309452976403369342500077568000000000 : Int) := by decide +kernel

theorem geometryRow089_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow089_jensenBoundDenominatorChars = some (48908824704270516063947526491453173212156855503855310062969363030488896966687801714457410466852818528835234320722915263810311092306413835090323985998657609881099454162840300083856681217085306323851359112058455973819981528911 : Int) := by decide +kernel

theorem geometryRow089_jensenBound_denominator_nonzero : (48908824704270516063947526491453173212156855503855310062969363030488896966687801714457410466852818528835234320722915263810311092306413835090323985998657609881099454162840300083856681217085306323851359112058455973819981528911 : Int) ≠ 0 := by decide +kernel

theorem geometryRow089_jensenBound_parse :
    parseRational geometryRow089_jensenBoundText = .ok geometryRowsTyped089.jensenBound :=
  original_rational_fraction_of_chars geometryRow089_jensenBoundNumeratorChars geometryRow089_jensenBoundDenominatorChars
    (5928618859423381739840123584089677967642363786059731814323535036877585825338368161127160147901018157985483359796301132146843189992835620449652522687664399167416030338940247377309452976403369342500077568000000000 : Int) (48908824704270516063947526491453173212156855503855310062969363030488896966687801714457410466852818528835234320722915263810311092306413835090323985998657609881099454162840300083856681217085306323851359112058455973819981528911 : Int)
    geometryRow089_jensenBound_numerator_no_slash geometryRow089_jensenBound_numerator_parse
    geometryRow089_jensenBound_denominator_parse geometryRow089_jensenBound_denominator_nonzero

theorem geometryRow089_jensenBound_read :
    rationalField geometryRowsJson089 "jensen_bound" = .ok geometryRowsTyped089.jensenBound :=
  original_rationalField_of_string geometryRowsJson089 "jensen_bound" geometryRow089_jensenBoundText
    geometryRowsTyped089.jensenBound geometryRow089_jensenBound_field geometryRow089_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_factorMaxima_before"
  err.flush

theorem geometryRow089_factorMaxima_read :
    rationalArrayField geometryRowsJson089 "factor_maxima" = .ok geometryRowsTyped089.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_gapWeightedMeans_before"
  err.flush

theorem geometryRow089_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson089 "gap_weighted_means" = .ok geometryRowsTyped089.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow089_floorChars : List Char := ['9', '6', '0', '3', '8', '6', '1', '4', '9', '7', '7', '9', '0', '4', '9', '4']
noncomputable def geometryRow089_floorText : String := String.ofList geometryRow089_floorChars

theorem geometryRow089_floor_text_read :
    geometryRowsJson089.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow089_floorText := by rfl

theorem geometryRow089_floor_chars_parse :
    SourceJson.intChars geometryRow089_floorChars = some (9603861497790494 : Int) := by decide +kernel

theorem geometryRow089_floor_parse :
    parseInteger geometryRow089_floorText = .ok geometryRowsTyped089.jensenFloorQ96 := by
  simp only [geometryRow089_floorText, parseInteger, String.toList_ofList, geometryRow089_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_089 :
    decodeGeometryRow geometryRowsJson089 = .ok geometryRowsTyped089 :=
  original_geometryRow_of_fields geometryRowsJson089 geometryRowsTyped089 geometryRow089_floorText
    geometryRow089_simplexId_read geometryRow089_vertexIds_read
    geometryRow089_physicalVolume_read geometryRow089_meanGap_read
    geometryRow089_factorMaxima_read geometryRow089_gapWeightedMeans_read
    geometryRow089_jensenBound_read geometryRow089_floor_text_read geometryRow089_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_089_original_decoder_complete"
  err.flush

theorem geometryRow089_shape :
    geometryRowsTyped089.simplexId = 89 ∧
    geometryRowsTyped089.vertexIds.size = 9 ∧ geometryRowsTyped089.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped089.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped089.factorMaxima.size = 10 ∧ geometryRowsTyped089.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson090 : SourceJson :=
  (SimplicesBlock011.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped090 : GeometryRow :=
  { simplexId := 90,
    vertexIds := #[32, 30, 28, 26, 25, 24, 22, 13, 4],
    physicalVolume := ((3319745815224792735099183741786443993053 : ℚ) / (22296250907280000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((984203 : ℚ) / (1354500000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((765619 : ℚ) / (10062500 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((425220032887 : ℚ) / (4984560000000 : ℚ)), ((10040451013 : ℚ) / (115920000000 : ℚ)), ((6591271909 : ℚ) / (54180000000 : ℚ)), ((157357123429 : ℚ) / (1661520000000 : ℚ)), ((156454229381 : ℚ) / (1661520000000 : ℚ)), ((173612706377 : ℚ) / (2492280000000 : ℚ)), ((5008041373 : ℚ) / (142416000000 : ℚ)), ((23927712413 : ℚ) / (712080000000 : ℚ)), ((158664923741 : ℚ) / (4984560000000 : ℚ)), ((685462027 : ℚ) / (23184000000 : ℚ))],
    jensenBound := ((820721004248237427794131130637018056705802906769763263540399570561503634391040000000000000 : ℚ) / (1177732745065513913270590580664969567468678228211629574204056989371245242025903605984154773301960764051 : ℚ)),
    jensenFloorQ96 := (55211351960696715 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_simplexId_before"
  err.flush

theorem geometryRow090_simplexId_read :
    geometryRowsJson090.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped090.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_vertexIds_before"
  err.flush

theorem geometryRow090_vertexIds_read :
    geometryRowsJson090.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped090.vertexIds := by decide +kernel

noncomputable def geometryRow090_physicalVolumeNumeratorChars : List Char := ['3', '3', '1', '9', '7', '4', '5', '8', '1', '5', '2', '2', '4', '7', '9', '2', '7', '3', '5', '0', '9', '9', '1', '8', '3', '7', '4', '1', '7', '8', '6', '4', '4', '3', '9', '9', '3', '0', '5', '3']
noncomputable def geometryRow090_physicalVolumeDenominatorChars : List Char := ['2', '2', '2', '9', '6', '2', '5', '0', '9', '0', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow090_physicalVolumeText : String := String.ofList (geometryRow090_physicalVolumeNumeratorChars ++ '/' :: geometryRow090_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_physicalVolume_before_field"
  err.flush

theorem geometryRow090_physicalVolume_field :
    geometryRowsJson090.getObjVal? "physical_volume" = .ok (.str geometryRow090_physicalVolumeText) := by rfl

theorem geometryRow090_physicalVolume_numerator_no_slash :
    geometryRow090_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow090_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow090_physicalVolumeNumeratorChars = some (3319745815224792735099183741786443993053 : Int) := by decide +kernel

theorem geometryRow090_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow090_physicalVolumeDenominatorChars = some (22296250907280000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow090_physicalVolume_denominator_nonzero : (22296250907280000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow090_physicalVolume_parse :
    parseRational geometryRow090_physicalVolumeText = .ok geometryRowsTyped090.physicalVolume :=
  original_rational_fraction_of_chars geometryRow090_physicalVolumeNumeratorChars geometryRow090_physicalVolumeDenominatorChars
    (3319745815224792735099183741786443993053 : Int) (22296250907280000000000000000000000000000000000000000000000000 : Int)
    geometryRow090_physicalVolume_numerator_no_slash geometryRow090_physicalVolume_numerator_parse
    geometryRow090_physicalVolume_denominator_parse geometryRow090_physicalVolume_denominator_nonzero

theorem geometryRow090_physicalVolume_read :
    rationalField geometryRowsJson090 "physical_volume" = .ok geometryRowsTyped090.physicalVolume :=
  original_rationalField_of_string geometryRowsJson090 "physical_volume" geometryRow090_physicalVolumeText
    geometryRowsTyped090.physicalVolume geometryRow090_physicalVolume_field geometryRow090_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_physicalVolume_complete"
  err.flush

noncomputable def geometryRow090_meanGapNumeratorChars : List Char := ['9', '8', '4', '2', '0', '3']
noncomputable def geometryRow090_meanGapDenominatorChars : List Char := ['1', '3', '5', '4', '5', '0', '0', '0', '0', '0']
noncomputable def geometryRow090_meanGapText : String := String.ofList (geometryRow090_meanGapNumeratorChars ++ '/' :: geometryRow090_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_meanGap_before_field"
  err.flush

theorem geometryRow090_meanGap_field :
    geometryRowsJson090.getObjVal? "mean_gap" = .ok (.str geometryRow090_meanGapText) := by rfl

theorem geometryRow090_meanGap_numerator_no_slash :
    geometryRow090_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow090_meanGap_numerator_parse :
    SourceJson.intChars geometryRow090_meanGapNumeratorChars = some (984203 : Int) := by decide +kernel

theorem geometryRow090_meanGap_denominator_parse :
    SourceJson.intChars geometryRow090_meanGapDenominatorChars = some (1354500000 : Int) := by decide +kernel

theorem geometryRow090_meanGap_denominator_nonzero : (1354500000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow090_meanGap_parse :
    parseRational geometryRow090_meanGapText = .ok geometryRowsTyped090.meanGap :=
  original_rational_fraction_of_chars geometryRow090_meanGapNumeratorChars geometryRow090_meanGapDenominatorChars
    (984203 : Int) (1354500000 : Int)
    geometryRow090_meanGap_numerator_no_slash geometryRow090_meanGap_numerator_parse
    geometryRow090_meanGap_denominator_parse geometryRow090_meanGap_denominator_nonzero

theorem geometryRow090_meanGap_read :
    rationalField geometryRowsJson090 "mean_gap" = .ok geometryRowsTyped090.meanGap :=
  original_rationalField_of_string geometryRowsJson090 "mean_gap" geometryRow090_meanGapText
    geometryRowsTyped090.meanGap geometryRow090_meanGap_field geometryRow090_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_meanGap_complete"
  err.flush

noncomputable def geometryRow090_jensenBoundNumeratorChars : List Char := ['8', '2', '0', '7', '2', '1', '0', '0', '4', '2', '4', '8', '2', '3', '7', '4', '2', '7', '7', '9', '4', '1', '3', '1', '1', '3', '0', '6', '3', '7', '0', '1', '8', '0', '5', '6', '7', '0', '5', '8', '0', '2', '9', '0', '6', '7', '6', '9', '7', '6', '3', '2', '6', '3', '5', '4', '0', '3', '9', '9', '5', '7', '0', '5', '6', '1', '5', '0', '3', '6', '3', '4', '3', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow090_jensenBoundDenominatorChars : List Char := ['1', '1', '7', '7', '7', '3', '2', '7', '4', '5', '0', '6', '5', '5', '1', '3', '9', '1', '3', '2', '7', '0', '5', '9', '0', '5', '8', '0', '6', '6', '4', '9', '6', '9', '5', '6', '7', '4', '6', '8', '6', '7', '8', '2', '2', '8', '2', '1', '1', '6', '2', '9', '5', '7', '4', '2', '0', '4', '0', '5', '6', '9', '8', '9', '3', '7', '1', '2', '4', '5', '2', '4', '2', '0', '2', '5', '9', '0', '3', '6', '0', '5', '9', '8', '4', '1', '5', '4', '7', '7', '3', '3', '0', '1', '9', '6', '0', '7', '6', '4', '0', '5', '1']
noncomputable def geometryRow090_jensenBoundText : String := String.ofList (geometryRow090_jensenBoundNumeratorChars ++ '/' :: geometryRow090_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_jensenBound_before_field"
  err.flush

theorem geometryRow090_jensenBound_field :
    geometryRowsJson090.getObjVal? "jensen_bound" = .ok (.str geometryRow090_jensenBoundText) := by rfl

theorem geometryRow090_jensenBound_numerator_no_slash :
    geometryRow090_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow090_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow090_jensenBoundNumeratorChars = some (820721004248237427794131130637018056705802906769763263540399570561503634391040000000000000 : Int) := by decide +kernel

theorem geometryRow090_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow090_jensenBoundDenominatorChars = some (1177732745065513913270590580664969567468678228211629574204056989371245242025903605984154773301960764051 : Int) := by decide +kernel

theorem geometryRow090_jensenBound_denominator_nonzero : (1177732745065513913270590580664969567468678228211629574204056989371245242025903605984154773301960764051 : Int) ≠ 0 := by decide +kernel

theorem geometryRow090_jensenBound_parse :
    parseRational geometryRow090_jensenBoundText = .ok geometryRowsTyped090.jensenBound :=
  original_rational_fraction_of_chars geometryRow090_jensenBoundNumeratorChars geometryRow090_jensenBoundDenominatorChars
    (820721004248237427794131130637018056705802906769763263540399570561503634391040000000000000 : Int) (1177732745065513913270590580664969567468678228211629574204056989371245242025903605984154773301960764051 : Int)
    geometryRow090_jensenBound_numerator_no_slash geometryRow090_jensenBound_numerator_parse
    geometryRow090_jensenBound_denominator_parse geometryRow090_jensenBound_denominator_nonzero

theorem geometryRow090_jensenBound_read :
    rationalField geometryRowsJson090 "jensen_bound" = .ok geometryRowsTyped090.jensenBound :=
  original_rationalField_of_string geometryRowsJson090 "jensen_bound" geometryRow090_jensenBoundText
    geometryRowsTyped090.jensenBound geometryRow090_jensenBound_field geometryRow090_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_factorMaxima_before"
  err.flush

theorem geometryRow090_factorMaxima_read :
    rationalArrayField geometryRowsJson090 "factor_maxima" = .ok geometryRowsTyped090.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_gapWeightedMeans_before"
  err.flush

theorem geometryRow090_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson090 "gap_weighted_means" = .ok geometryRowsTyped090.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow090_floorChars : List Char := ['5', '5', '2', '1', '1', '3', '5', '1', '9', '6', '0', '6', '9', '6', '7', '1', '5']
noncomputable def geometryRow090_floorText : String := String.ofList geometryRow090_floorChars

theorem geometryRow090_floor_text_read :
    geometryRowsJson090.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow090_floorText := by rfl

theorem geometryRow090_floor_chars_parse :
    SourceJson.intChars geometryRow090_floorChars = some (55211351960696715 : Int) := by decide +kernel

theorem geometryRow090_floor_parse :
    parseInteger geometryRow090_floorText = .ok geometryRowsTyped090.jensenFloorQ96 := by
  simp only [geometryRow090_floorText, parseInteger, String.toList_ofList, geometryRow090_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_090 :
    decodeGeometryRow geometryRowsJson090 = .ok geometryRowsTyped090 :=
  original_geometryRow_of_fields geometryRowsJson090 geometryRowsTyped090 geometryRow090_floorText
    geometryRow090_simplexId_read geometryRow090_vertexIds_read
    geometryRow090_physicalVolume_read geometryRow090_meanGap_read
    geometryRow090_factorMaxima_read geometryRow090_gapWeightedMeans_read
    geometryRow090_jensenBound_read geometryRow090_floor_text_read geometryRow090_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_090_original_decoder_complete"
  err.flush

theorem geometryRow090_shape :
    geometryRowsTyped090.simplexId = 90 ∧
    geometryRowsTyped090.vertexIds.size = 9 ∧ geometryRowsTyped090.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped090.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped090.factorMaxima.size = 10 ∧ geometryRowsTyped090.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson091 : SourceJson :=
  (SimplicesBlock011.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped091 : GeometryRow :=
  { simplexId := 91,
    vertexIds := #[32, 30, 29, 20, 6, 4, 2, 1, 0],
    physicalVolume := ((269600783200723601941797910681526889654968809 : ℚ) / (3360124004158881792000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((15917262430661 : ℚ) / (4307213680000000 : ℚ)),
    factorMaxima := #[((5390597 : ℚ) / (60000000 : ℚ)), ((17390541 : ℚ) / (184000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((99250204621801412358603465607 : ℚ) / (1165503858321382880922160000000 : ℚ)), ((7766758864520346175181196151 : ℚ) / (87122381435983770168600000000 : ℚ)), ((94818761776986952183629368699 : ℚ) / (819494900382222338148393750000 : ℚ)), ((407684700523787199141215204203 : ℚ) / (4370639468705185803458100000000 : ℚ)), ((1193059637364358599728136734323 : ℚ) / (13111918406115557410374300000000 : ℚ)), ((34119079695350753542346447717 : ℚ) / (476797032949656633104520000000 : ℚ)), ((8540962811674037856908356327 : ℚ) / (238398516474828316552260000000 : ℚ)), ((3397197175083627967347501461 : ℚ) / (95359406589931326620904000000 : ℚ)), ((16726855671142506305248433089 : ℚ) / (476797032949656633104520000000 : ℚ)), ((294379568052664665404361093 : ℚ) / (9680264603998196685400000000 : ℚ))],
    jensenBound := ((94318932257306054757276229839957428400346092793273680951913173173998291276064551555135382254042218934907779041022980400391256943122097547256935111824264398872048953417590399906429212688980270792205241228135493630507944861765850346151982060314122818976450468750000000000 : ℚ) / (57766717637951025304515983346246208889609318330226640902501044236059934652371276156534685651092272133613379505455019395528837715139949282045345297492862477314526471290021419661631330027332165574615564237752655926521801041184952100728415577572380977422963322280687930888396530643886147 : ℚ)),
    jensenFloorQ96 := (129360226763938 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_simplexId_before"
  err.flush

theorem geometryRow091_simplexId_read :
    geometryRowsJson091.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped091.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_vertexIds_before"
  err.flush

theorem geometryRow091_vertexIds_read :
    geometryRowsJson091.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped091.vertexIds := by decide +kernel

noncomputable def geometryRow091_physicalVolumeNumeratorChars : List Char := ['2', '6', '9', '6', '0', '0', '7', '8', '3', '2', '0', '0', '7', '2', '3', '6', '0', '1', '9', '4', '1', '7', '9', '7', '9', '1', '0', '6', '8', '1', '5', '2', '6', '8', '8', '9', '6', '5', '4', '9', '6', '8', '8', '0', '9']
noncomputable def geometryRow091_physicalVolumeDenominatorChars : List Char := ['3', '3', '6', '0', '1', '2', '4', '0', '0', '4', '1', '5', '8', '8', '8', '1', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow091_physicalVolumeText : String := String.ofList (geometryRow091_physicalVolumeNumeratorChars ++ '/' :: geometryRow091_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_physicalVolume_before_field"
  err.flush

theorem geometryRow091_physicalVolume_field :
    geometryRowsJson091.getObjVal? "physical_volume" = .ok (.str geometryRow091_physicalVolumeText) := by rfl

theorem geometryRow091_physicalVolume_numerator_no_slash :
    geometryRow091_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow091_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow091_physicalVolumeNumeratorChars = some (269600783200723601941797910681526889654968809 : Int) := by decide +kernel

theorem geometryRow091_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow091_physicalVolumeDenominatorChars = some (3360124004158881792000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow091_physicalVolume_denominator_nonzero : (3360124004158881792000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow091_physicalVolume_parse :
    parseRational geometryRow091_physicalVolumeText = .ok geometryRowsTyped091.physicalVolume :=
  original_rational_fraction_of_chars geometryRow091_physicalVolumeNumeratorChars geometryRow091_physicalVolumeDenominatorChars
    (269600783200723601941797910681526889654968809 : Int) (3360124004158881792000000000000000000000000000000000000000000000000000 : Int)
    geometryRow091_physicalVolume_numerator_no_slash geometryRow091_physicalVolume_numerator_parse
    geometryRow091_physicalVolume_denominator_parse geometryRow091_physicalVolume_denominator_nonzero

theorem geometryRow091_physicalVolume_read :
    rationalField geometryRowsJson091 "physical_volume" = .ok geometryRowsTyped091.physicalVolume :=
  original_rationalField_of_string geometryRowsJson091 "physical_volume" geometryRow091_physicalVolumeText
    geometryRowsTyped091.physicalVolume geometryRow091_physicalVolume_field geometryRow091_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_physicalVolume_complete"
  err.flush

noncomputable def geometryRow091_meanGapNumeratorChars : List Char := ['1', '5', '9', '1', '7', '2', '6', '2', '4', '3', '0', '6', '6', '1']
noncomputable def geometryRow091_meanGapDenominatorChars : List Char := ['4', '3', '0', '7', '2', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow091_meanGapText : String := String.ofList (geometryRow091_meanGapNumeratorChars ++ '/' :: geometryRow091_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_meanGap_before_field"
  err.flush

theorem geometryRow091_meanGap_field :
    geometryRowsJson091.getObjVal? "mean_gap" = .ok (.str geometryRow091_meanGapText) := by rfl

theorem geometryRow091_meanGap_numerator_no_slash :
    geometryRow091_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow091_meanGap_numerator_parse :
    SourceJson.intChars geometryRow091_meanGapNumeratorChars = some (15917262430661 : Int) := by decide +kernel

theorem geometryRow091_meanGap_denominator_parse :
    SourceJson.intChars geometryRow091_meanGapDenominatorChars = some (4307213680000000 : Int) := by decide +kernel

theorem geometryRow091_meanGap_denominator_nonzero : (4307213680000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow091_meanGap_parse :
    parseRational geometryRow091_meanGapText = .ok geometryRowsTyped091.meanGap :=
  original_rational_fraction_of_chars geometryRow091_meanGapNumeratorChars geometryRow091_meanGapDenominatorChars
    (15917262430661 : Int) (4307213680000000 : Int)
    geometryRow091_meanGap_numerator_no_slash geometryRow091_meanGap_numerator_parse
    geometryRow091_meanGap_denominator_parse geometryRow091_meanGap_denominator_nonzero

theorem geometryRow091_meanGap_read :
    rationalField geometryRowsJson091 "mean_gap" = .ok geometryRowsTyped091.meanGap :=
  original_rationalField_of_string geometryRowsJson091 "mean_gap" geometryRow091_meanGapText
    geometryRowsTyped091.meanGap geometryRow091_meanGap_field geometryRow091_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_meanGap_complete"
  err.flush

noncomputable def geometryRow091_jensenBoundNumeratorChars : List Char := ['9', '4', '3', '1', '8', '9', '3', '2', '2', '5', '7', '3', '0', '6', '0', '5', '4', '7', '5', '7', '2', '7', '6', '2', '2', '9', '8', '3', '9', '9', '5', '7', '4', '2', '8', '4', '0', '0', '3', '4', '6', '0', '9', '2', '7', '9', '3', '2', '7', '3', '6', '8', '0', '9', '5', '1', '9', '1', '3', '1', '7', '3', '1', '7', '3', '9', '9', '8', '2', '9', '1', '2', '7', '6', '0', '6', '4', '5', '5', '1', '5', '5', '5', '1', '3', '5', '3', '8', '2', '2', '5', '4', '0', '4', '2', '2', '1', '8', '9', '3', '4', '9', '0', '7', '7', '7', '9', '0', '4', '1', '0', '2', '2', '9', '8', '0', '4', '0', '0', '3', '9', '1', '2', '5', '6', '9', '4', '3', '1', '2', '2', '0', '9', '7', '5', '4', '7', '2', '5', '6', '9', '3', '5', '1', '1', '1', '8', '2', '4', '2', '6', '4', '3', '9', '8', '8', '7', '2', '0', '4', '8', '9', '5', '3', '4', '1', '7', '5', '9', '0', '3', '9', '9', '9', '0', '6', '4', '2', '9', '2', '1', '2', '6', '8', '8', '9', '8', '0', '2', '7', '0', '7', '9', '2', '2', '0', '5', '2', '4', '1', '2', '2', '8', '1', '3', '5', '4', '9', '3', '6', '3', '0', '5', '0', '7', '9', '4', '4', '8', '6', '1', '7', '6', '5', '8', '5', '0', '3', '4', '6', '1', '5', '1', '9', '8', '2', '0', '6', '0', '3', '1', '4', '1', '2', '2', '8', '1', '8', '9', '7', '6', '4', '5', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow091_jensenBoundDenominatorChars : List Char := ['5', '7', '7', '6', '6', '7', '1', '7', '6', '3', '7', '9', '5', '1', '0', '2', '5', '3', '0', '4', '5', '1', '5', '9', '8', '3', '3', '4', '6', '2', '4', '6', '2', '0', '8', '8', '8', '9', '6', '0', '9', '3', '1', '8', '3', '3', '0', '2', '2', '6', '6', '4', '0', '9', '0', '2', '5', '0', '1', '0', '4', '4', '2', '3', '6', '0', '5', '9', '9', '3', '4', '6', '5', '2', '3', '7', '1', '2', '7', '6', '1', '5', '6', '5', '3', '4', '6', '8', '5', '6', '5', '1', '0', '9', '2', '2', '7', '2', '1', '3', '3', '6', '1', '3', '3', '7', '9', '5', '0', '5', '4', '5', '5', '0', '1', '9', '3', '9', '5', '5', '2', '8', '8', '3', '7', '7', '1', '5', '1', '3', '9', '9', '4', '9', '2', '8', '2', '0', '4', '5', '3', '4', '5', '2', '9', '7', '4', '9', '2', '8', '6', '2', '4', '7', '7', '3', '1', '4', '5', '2', '6', '4', '7', '1', '2', '9', '0', '0', '2', '1', '4', '1', '9', '6', '6', '1', '6', '3', '1', '3', '3', '0', '0', '2', '7', '3', '3', '2', '1', '6', '5', '5', '7', '4', '6', '1', '5', '5', '6', '4', '2', '3', '7', '7', '5', '2', '6', '5', '5', '9', '2', '6', '5', '2', '1', '8', '0', '1', '0', '4', '1', '1', '8', '4', '9', '5', '2', '1', '0', '0', '7', '2', '8', '4', '1', '5', '5', '7', '7', '5', '7', '2', '3', '8', '0', '9', '7', '7', '4', '2', '2', '9', '6', '3', '3', '2', '2', '2', '8', '0', '6', '8', '7', '9', '3', '0', '8', '8', '8', '3', '9', '6', '5', '3', '0', '6', '4', '3', '8', '8', '6', '1', '4', '7']
noncomputable def geometryRow091_jensenBoundText : String := String.ofList (geometryRow091_jensenBoundNumeratorChars ++ '/' :: geometryRow091_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_jensenBound_before_field"
  err.flush

theorem geometryRow091_jensenBound_field :
    geometryRowsJson091.getObjVal? "jensen_bound" = .ok (.str geometryRow091_jensenBoundText) := by rfl

theorem geometryRow091_jensenBound_numerator_no_slash :
    geometryRow091_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow091_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow091_jensenBoundNumeratorChars = some (94318932257306054757276229839957428400346092793273680951913173173998291276064551555135382254042218934907779041022980400391256943122097547256935111824264398872048953417590399906429212688980270792205241228135493630507944861765850346151982060314122818976450468750000000000 : Int) := by decide +kernel

theorem geometryRow091_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow091_jensenBoundDenominatorChars = some (57766717637951025304515983346246208889609318330226640902501044236059934652371276156534685651092272133613379505455019395528837715139949282045345297492862477314526471290021419661631330027332165574615564237752655926521801041184952100728415577572380977422963322280687930888396530643886147 : Int) := by decide +kernel

theorem geometryRow091_jensenBound_denominator_nonzero : (57766717637951025304515983346246208889609318330226640902501044236059934652371276156534685651092272133613379505455019395528837715139949282045345297492862477314526471290021419661631330027332165574615564237752655926521801041184952100728415577572380977422963322280687930888396530643886147 : Int) ≠ 0 := by decide +kernel

theorem geometryRow091_jensenBound_parse :
    parseRational geometryRow091_jensenBoundText = .ok geometryRowsTyped091.jensenBound :=
  original_rational_fraction_of_chars geometryRow091_jensenBoundNumeratorChars geometryRow091_jensenBoundDenominatorChars
    (94318932257306054757276229839957428400346092793273680951913173173998291276064551555135382254042218934907779041022980400391256943122097547256935111824264398872048953417590399906429212688980270792205241228135493630507944861765850346151982060314122818976450468750000000000 : Int) (57766717637951025304515983346246208889609318330226640902501044236059934652371276156534685651092272133613379505455019395528837715139949282045345297492862477314526471290021419661631330027332165574615564237752655926521801041184952100728415577572380977422963322280687930888396530643886147 : Int)
    geometryRow091_jensenBound_numerator_no_slash geometryRow091_jensenBound_numerator_parse
    geometryRow091_jensenBound_denominator_parse geometryRow091_jensenBound_denominator_nonzero

theorem geometryRow091_jensenBound_read :
    rationalField geometryRowsJson091 "jensen_bound" = .ok geometryRowsTyped091.jensenBound :=
  original_rationalField_of_string geometryRowsJson091 "jensen_bound" geometryRow091_jensenBoundText
    geometryRowsTyped091.jensenBound geometryRow091_jensenBound_field geometryRow091_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_factorMaxima_before"
  err.flush

theorem geometryRow091_factorMaxima_read :
    rationalArrayField geometryRowsJson091 "factor_maxima" = .ok geometryRowsTyped091.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_gapWeightedMeans_before"
  err.flush

theorem geometryRow091_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson091 "gap_weighted_means" = .ok geometryRowsTyped091.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow091_floorChars : List Char := ['1', '2', '9', '3', '6', '0', '2', '2', '6', '7', '6', '3', '9', '3', '8']
noncomputable def geometryRow091_floorText : String := String.ofList geometryRow091_floorChars

theorem geometryRow091_floor_text_read :
    geometryRowsJson091.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow091_floorText := by rfl

theorem geometryRow091_floor_chars_parse :
    SourceJson.intChars geometryRow091_floorChars = some (129360226763938 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_091_original_decoder_complete"
  err.flush

theorem geometryRow091_shape :
    geometryRowsTyped091.simplexId = 91 ∧
    geometryRowsTyped091.vertexIds.size = 9 ∧ geometryRowsTyped091.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped091.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped091.factorMaxima.size = 10 ∧ geometryRowsTyped091.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson092 : SourceJson :=
  (SimplicesBlock011.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped092 : GeometryRow :=
  { simplexId := 92,
    vertexIds := #[32, 30, 29, 20, 15, 4, 2, 1, 0],
    physicalVolume := ((124174286470167848810538374851445804948005519 : ℚ) / (119766796187841331200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1133902280579 : ℚ) / (383811120000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((321240863311174775903675551 : ℚ) / (3699236586376432027080000000 : ℚ)), ((11080932384632079624789703 : ℚ) / (122898225461011030800000000 : ℚ)), ((2867398442157493322913832831 : ℚ) / (24661577242509546847200000000 : ℚ)), ((6819203687761634325846778943 : ℚ) / (73984731727528640541600000000 : ℚ)), ((6657176157001330487308603291 : ℚ) / (73984731727528640541600000000 : ℚ)), ((6486017587786699371488143 : ℚ) / (89678462700034715808000000 : ℚ)), ((23972352034286245784047447 : ℚ) / (672588470250260368560000000 : ℚ)), ((190650609154998627850301 : ℚ) / (5380707762002082948480000 : ℚ)), ((23465786982750497845445977 : ℚ) / (672588470250260368560000000 : ℚ)), ((3778982835256367993813261 : ℚ) / (122898225461011030800000000 : ℚ))],
    jensenBound := ((1833814517356096316795109505903141699698710234514538508710213988269899048265638384857453967644448773055775060584115821934085712930166189027185356168820153006619818015957139985423445535019030600680171751677584496729017097634109849600000000000000 : ℚ) / (110729456973359739349562453046985190378693608873967931070367840690646432467605716209597146192683572876076689630652271836017140595210682964550234794178922068866628623327591242262338750976689016634672159717608972313747377157635188890388207446640792701837505553 : ℚ)),
    jensenFloorQ96 := (1312114757657134 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_simplexId_before"
  err.flush

theorem geometryRow092_simplexId_read :
    geometryRowsJson092.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped092.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_vertexIds_before"
  err.flush

theorem geometryRow092_vertexIds_read :
    geometryRowsJson092.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped092.vertexIds := by decide +kernel

noncomputable def geometryRow092_physicalVolumeNumeratorChars : List Char := ['1', '2', '4', '1', '7', '4', '2', '8', '6', '4', '7', '0', '1', '6', '7', '8', '4', '8', '8', '1', '0', '5', '3', '8', '3', '7', '4', '8', '5', '1', '4', '4', '5', '8', '0', '4', '9', '4', '8', '0', '0', '5', '5', '1', '9']
noncomputable def geometryRow092_physicalVolumeDenominatorChars : List Char := ['1', '1', '9', '7', '6', '6', '7', '9', '6', '1', '8', '7', '8', '4', '1', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow092_physicalVolumeText : String := String.ofList (geometryRow092_physicalVolumeNumeratorChars ++ '/' :: geometryRow092_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_physicalVolume_before_field"
  err.flush

theorem geometryRow092_physicalVolume_field :
    geometryRowsJson092.getObjVal? "physical_volume" = .ok (.str geometryRow092_physicalVolumeText) := by rfl

theorem geometryRow092_physicalVolume_numerator_no_slash :
    geometryRow092_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow092_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow092_physicalVolumeNumeratorChars = some (124174286470167848810538374851445804948005519 : Int) := by decide +kernel

theorem geometryRow092_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow092_physicalVolumeDenominatorChars = some (119766796187841331200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow092_physicalVolume_denominator_nonzero : (119766796187841331200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow092_physicalVolume_parse :
    parseRational geometryRow092_physicalVolumeText = .ok geometryRowsTyped092.physicalVolume :=
  original_rational_fraction_of_chars geometryRow092_physicalVolumeNumeratorChars geometryRow092_physicalVolumeDenominatorChars
    (124174286470167848810538374851445804948005519 : Int) (119766796187841331200000000000000000000000000000000000000000000000000 : Int)
    geometryRow092_physicalVolume_numerator_no_slash geometryRow092_physicalVolume_numerator_parse
    geometryRow092_physicalVolume_denominator_parse geometryRow092_physicalVolume_denominator_nonzero

theorem geometryRow092_physicalVolume_read :
    rationalField geometryRowsJson092 "physical_volume" = .ok geometryRowsTyped092.physicalVolume :=
  original_rationalField_of_string geometryRowsJson092 "physical_volume" geometryRow092_physicalVolumeText
    geometryRowsTyped092.physicalVolume geometryRow092_physicalVolume_field geometryRow092_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_physicalVolume_complete"
  err.flush

noncomputable def geometryRow092_meanGapNumeratorChars : List Char := ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9']
noncomputable def geometryRow092_meanGapDenominatorChars : List Char := ['3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow092_meanGapText : String := String.ofList (geometryRow092_meanGapNumeratorChars ++ '/' :: geometryRow092_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_meanGap_before_field"
  err.flush

theorem geometryRow092_meanGap_field :
    geometryRowsJson092.getObjVal? "mean_gap" = .ok (.str geometryRow092_meanGapText) := by rfl

theorem geometryRow092_meanGap_numerator_no_slash :
    geometryRow092_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow092_meanGap_numerator_parse :
    SourceJson.intChars geometryRow092_meanGapNumeratorChars = some (1133902280579 : Int) := by decide +kernel

theorem geometryRow092_meanGap_denominator_parse :
    SourceJson.intChars geometryRow092_meanGapDenominatorChars = some (383811120000000 : Int) := by decide +kernel

theorem geometryRow092_meanGap_denominator_nonzero : (383811120000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow092_meanGap_parse :
    parseRational geometryRow092_meanGapText = .ok geometryRowsTyped092.meanGap :=
  original_rational_fraction_of_chars geometryRow092_meanGapNumeratorChars geometryRow092_meanGapDenominatorChars
    (1133902280579 : Int) (383811120000000 : Int)
    geometryRow092_meanGap_numerator_no_slash geometryRow092_meanGap_numerator_parse
    geometryRow092_meanGap_denominator_parse geometryRow092_meanGap_denominator_nonzero

theorem geometryRow092_meanGap_read :
    rationalField geometryRowsJson092 "mean_gap" = .ok geometryRowsTyped092.meanGap :=
  original_rationalField_of_string geometryRowsJson092 "mean_gap" geometryRow092_meanGapText
    geometryRowsTyped092.meanGap geometryRow092_meanGap_field geometryRow092_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_meanGap_complete"
  err.flush

noncomputable def geometryRow092_jensenBoundNumeratorChars : List Char := ['1', '8', '3', '3', '8', '1', '4', '5', '1', '7', '3', '5', '6', '0', '9', '6', '3', '1', '6', '7', '9', '5', '1', '0', '9', '5', '0', '5', '9', '0', '3', '1', '4', '1', '6', '9', '9', '6', '9', '8', '7', '1', '0', '2', '3', '4', '5', '1', '4', '5', '3', '8', '5', '0', '8', '7', '1', '0', '2', '1', '3', '9', '8', '8', '2', '6', '9', '8', '9', '9', '0', '4', '8', '2', '6', '5', '6', '3', '8', '3', '8', '4', '8', '5', '7', '4', '5', '3', '9', '6', '7', '6', '4', '4', '4', '4', '8', '7', '7', '3', '0', '5', '5', '7', '7', '5', '0', '6', '0', '5', '8', '4', '1', '1', '5', '8', '2', '1', '9', '3', '4', '0', '8', '5', '7', '1', '2', '9', '3', '0', '1', '6', '6', '1', '8', '9', '0', '2', '7', '1', '8', '5', '3', '5', '6', '1', '6', '8', '8', '2', '0', '1', '5', '3', '0', '0', '6', '6', '1', '9', '8', '1', '8', '0', '1', '5', '9', '5', '7', '1', '3', '9', '9', '8', '5', '4', '2', '3', '4', '4', '5', '5', '3', '5', '0', '1', '9', '0', '3', '0', '6', '0', '0', '6', '8', '0', '1', '7', '1', '7', '5', '1', '6', '7', '7', '5', '8', '4', '4', '9', '6', '7', '2', '9', '0', '1', '7', '0', '9', '7', '6', '3', '4', '1', '0', '9', '8', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow092_jensenBoundDenominatorChars : List Char := ['1', '1', '0', '7', '2', '9', '4', '5', '6', '9', '7', '3', '3', '5', '9', '7', '3', '9', '3', '4', '9', '5', '6', '2', '4', '5', '3', '0', '4', '6', '9', '8', '5', '1', '9', '0', '3', '7', '8', '6', '9', '3', '6', '0', '8', '8', '7', '3', '9', '6', '7', '9', '3', '1', '0', '7', '0', '3', '6', '7', '8', '4', '0', '6', '9', '0', '6', '4', '6', '4', '3', '2', '4', '6', '7', '6', '0', '5', '7', '1', '6', '2', '0', '9', '5', '9', '7', '1', '4', '6', '1', '9', '2', '6', '8', '3', '5', '7', '2', '8', '7', '6', '0', '7', '6', '6', '8', '9', '6', '3', '0', '6', '5', '2', '2', '7', '1', '8', '3', '6', '0', '1', '7', '1', '4', '0', '5', '9', '5', '2', '1', '0', '6', '8', '2', '9', '6', '4', '5', '5', '0', '2', '3', '4', '7', '9', '4', '1', '7', '8', '9', '2', '2', '0', '6', '8', '8', '6', '6', '6', '2', '8', '6', '2', '3', '3', '2', '7', '5', '9', '1', '2', '4', '2', '2', '6', '2', '3', '3', '8', '7', '5', '0', '9', '7', '6', '6', '8', '9', '0', '1', '6', '6', '3', '4', '6', '7', '2', '1', '5', '9', '7', '1', '7', '6', '0', '8', '9', '7', '2', '3', '1', '3', '7', '4', '7', '3', '7', '7', '1', '5', '7', '6', '3', '5', '1', '8', '8', '8', '9', '0', '3', '8', '8', '2', '0', '7', '4', '4', '6', '6', '4', '0', '7', '9', '2', '7', '0', '1', '8', '3', '7', '5', '0', '5', '5', '5', '3']
noncomputable def geometryRow092_jensenBoundText : String := String.ofList (geometryRow092_jensenBoundNumeratorChars ++ '/' :: geometryRow092_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_jensenBound_before_field"
  err.flush

theorem geometryRow092_jensenBound_field :
    geometryRowsJson092.getObjVal? "jensen_bound" = .ok (.str geometryRow092_jensenBoundText) := by rfl

theorem geometryRow092_jensenBound_numerator_no_slash :
    geometryRow092_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow092_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow092_jensenBoundNumeratorChars = some (1833814517356096316795109505903141699698710234514538508710213988269899048265638384857453967644448773055775060584115821934085712930166189027185356168820153006619818015957139985423445535019030600680171751677584496729017097634109849600000000000000 : Int) := by decide +kernel

theorem geometryRow092_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow092_jensenBoundDenominatorChars = some (110729456973359739349562453046985190378693608873967931070367840690646432467605716209597146192683572876076689630652271836017140595210682964550234794178922068866628623327591242262338750976689016634672159717608972313747377157635188890388207446640792701837505553 : Int) := by decide +kernel

theorem geometryRow092_jensenBound_denominator_nonzero : (110729456973359739349562453046985190378693608873967931070367840690646432467605716209597146192683572876076689630652271836017140595210682964550234794178922068866628623327591242262338750976689016634672159717608972313747377157635188890388207446640792701837505553 : Int) ≠ 0 := by decide +kernel

theorem geometryRow092_jensenBound_parse :
    parseRational geometryRow092_jensenBoundText = .ok geometryRowsTyped092.jensenBound :=
  original_rational_fraction_of_chars geometryRow092_jensenBoundNumeratorChars geometryRow092_jensenBoundDenominatorChars
    (1833814517356096316795109505903141699698710234514538508710213988269899048265638384857453967644448773055775060584115821934085712930166189027185356168820153006619818015957139985423445535019030600680171751677584496729017097634109849600000000000000 : Int) (110729456973359739349562453046985190378693608873967931070367840690646432467605716209597146192683572876076689630652271836017140595210682964550234794178922068866628623327591242262338750976689016634672159717608972313747377157635188890388207446640792701837505553 : Int)
    geometryRow092_jensenBound_numerator_no_slash geometryRow092_jensenBound_numerator_parse
    geometryRow092_jensenBound_denominator_parse geometryRow092_jensenBound_denominator_nonzero

theorem geometryRow092_jensenBound_read :
    rationalField geometryRowsJson092 "jensen_bound" = .ok geometryRowsTyped092.jensenBound :=
  original_rationalField_of_string geometryRowsJson092 "jensen_bound" geometryRow092_jensenBoundText
    geometryRowsTyped092.jensenBound geometryRow092_jensenBound_field geometryRow092_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_factorMaxima_before"
  err.flush

theorem geometryRow092_factorMaxima_read :
    rationalArrayField geometryRowsJson092 "factor_maxima" = .ok geometryRowsTyped092.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_gapWeightedMeans_before"
  err.flush

theorem geometryRow092_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson092 "gap_weighted_means" = .ok geometryRowsTyped092.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow092_floorChars : List Char := ['1', '3', '1', '2', '1', '1', '4', '7', '5', '7', '6', '5', '7', '1', '3', '4']
noncomputable def geometryRow092_floorText : String := String.ofList geometryRow092_floorChars

theorem geometryRow092_floor_text_read :
    geometryRowsJson092.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow092_floorText := by rfl

theorem geometryRow092_floor_chars_parse :
    SourceJson.intChars geometryRow092_floorChars = some (1312114757657134 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_092_original_decoder_complete"
  err.flush

theorem geometryRow092_shape :
    geometryRowsTyped092.simplexId = 92 ∧
    geometryRowsTyped092.vertexIds.size = 9 ∧ geometryRowsTyped092.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped092.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped092.factorMaxima.size = 10 ∧ geometryRowsTyped092.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson093 : SourceJson :=
  (SimplicesBlock011.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped093 : GeometryRow :=
  { simplexId := 93,
    vertexIds := #[32, 30, 29, 20, 15, 13, 4, 1, 0],
    physicalVolume := ((1229234216250277142980847432527506329777297959 : ℚ) / (130994933330451456000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((209797667262404268926609 : ℚ) / (2400113918032243459200000 : ℚ)), ((89761866054702036464029 : ℚ) / (996725049016712400000000 : ℚ)), ((1015614024030373616137811 : ℚ) / (8696064920406679200000000 : ℚ)), ((54824155471877447819820329 : ℚ) / (600028479508060864800000000 : ℚ)), ((53510085248867149244935573 : ℚ) / (600028479508060864800000000 : ℚ)), ((264186925083919920808157 : ℚ) / (3636536239442793120000000 : ℚ)), ((195644124136632792202861 : ℚ) / (5454804359164189680000000 : ℚ)), ((38884420223705133667619 : ℚ) / (1090960871832837936000000 : ℚ)), ((191457517720996263325951 : ℚ) / (5454804359164189680000000 : ℚ)), ((30612733125974194775423 : ℚ) / (996725049016712400000000 : ℚ))],
    jensenBound := ((72915582871907500628556520577806153324292640464189651025743791619746354461118323884231539912621937746883137770331693338209949904734333622841879686137250994914964676103250589135779794658545139978329967885392281600000000000000 : ℚ) / (660932482348772540209614742555989180514582180608755920860345771382483986256843400611954506599723440573801013315471847482600585561088795399465892492389368158423918103996977219875189800720334276588132510982605869240753424082819306891749193 : ℚ)),
    jensenFloorQ96 := (8740632067390666 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_simplexId_before"
  err.flush

theorem geometryRow093_simplexId_read :
    geometryRowsJson093.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped093.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_vertexIds_before"
  err.flush

theorem geometryRow093_vertexIds_read :
    geometryRowsJson093.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped093.vertexIds := by decide +kernel

noncomputable def geometryRow093_physicalVolumeNumeratorChars : List Char := ['1', '2', '2', '9', '2', '3', '4', '2', '1', '6', '2', '5', '0', '2', '7', '7', '1', '4', '2', '9', '8', '0', '8', '4', '7', '4', '3', '2', '5', '2', '7', '5', '0', '6', '3', '2', '9', '7', '7', '7', '2', '9', '7', '9', '5', '9']
noncomputable def geometryRow093_physicalVolumeDenominatorChars : List Char := ['1', '3', '0', '9', '9', '4', '9', '3', '3', '3', '3', '0', '4', '5', '1', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow093_physicalVolumeText : String := String.ofList (geometryRow093_physicalVolumeNumeratorChars ++ '/' :: geometryRow093_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_physicalVolume_before_field"
  err.flush

theorem geometryRow093_physicalVolume_field :
    geometryRowsJson093.getObjVal? "physical_volume" = .ok (.str geometryRow093_physicalVolumeText) := by rfl

theorem geometryRow093_physicalVolume_numerator_no_slash :
    geometryRow093_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow093_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow093_physicalVolumeNumeratorChars = some (1229234216250277142980847432527506329777297959 : Int) := by decide +kernel

theorem geometryRow093_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow093_physicalVolumeDenominatorChars = some (130994933330451456000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow093_physicalVolume_denominator_nonzero : (130994933330451456000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow093_physicalVolume_parse :
    parseRational geometryRow093_physicalVolumeText = .ok geometryRowsTyped093.physicalVolume :=
  original_rational_fraction_of_chars geometryRow093_physicalVolumeNumeratorChars geometryRow093_physicalVolumeDenominatorChars
    (1229234216250277142980847432527506329777297959 : Int) (130994933330451456000000000000000000000000000000000000000000000000000 : Int)
    geometryRow093_physicalVolume_numerator_no_slash geometryRow093_physicalVolume_numerator_parse
    geometryRow093_physicalVolume_denominator_parse geometryRow093_physicalVolume_denominator_nonzero

theorem geometryRow093_physicalVolume_read :
    rationalField geometryRowsJson093 "physical_volume" = .ok geometryRowsTyped093.physicalVolume :=
  original_rationalField_of_string geometryRowsJson093 "physical_volume" geometryRow093_physicalVolumeText
    geometryRowsTyped093.physicalVolume geometryRow093_physicalVolume_field geometryRow093_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_physicalVolume_complete"
  err.flush

noncomputable def geometryRow093_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow093_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow093_meanGapText : String := String.ofList (geometryRow093_meanGapNumeratorChars ++ '/' :: geometryRow093_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_meanGap_before_field"
  err.flush

theorem geometryRow093_meanGap_field :
    geometryRowsJson093.getObjVal? "mean_gap" = .ok (.str geometryRow093_meanGapText) := by rfl

theorem geometryRow093_meanGap_numerator_no_slash :
    geometryRow093_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow093_meanGap_numerator_parse :
    SourceJson.intChars geometryRow093_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow093_meanGap_denominator_parse :
    SourceJson.intChars geometryRow093_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow093_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow093_meanGap_parse :
    parseRational geometryRow093_meanGapText = .ok geometryRowsTyped093.meanGap :=
  original_rational_fraction_of_chars geometryRow093_meanGapNumeratorChars geometryRow093_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow093_meanGap_numerator_no_slash geometryRow093_meanGap_numerator_parse
    geometryRow093_meanGap_denominator_parse geometryRow093_meanGap_denominator_nonzero

theorem geometryRow093_meanGap_read :
    rationalField geometryRowsJson093 "mean_gap" = .ok geometryRowsTyped093.meanGap :=
  original_rationalField_of_string geometryRowsJson093 "mean_gap" geometryRow093_meanGapText
    geometryRowsTyped093.meanGap geometryRow093_meanGap_field geometryRow093_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_meanGap_complete"
  err.flush

noncomputable def geometryRow093_jensenBoundNumeratorChars : List Char := ['7', '2', '9', '1', '5', '5', '8', '2', '8', '7', '1', '9', '0', '7', '5', '0', '0', '6', '2', '8', '5', '5', '6', '5', '2', '0', '5', '7', '7', '8', '0', '6', '1', '5', '3', '3', '2', '4', '2', '9', '2', '6', '4', '0', '4', '6', '4', '1', '8', '9', '6', '5', '1', '0', '2', '5', '7', '4', '3', '7', '9', '1', '6', '1', '9', '7', '4', '6', '3', '5', '4', '4', '6', '1', '1', '1', '8', '3', '2', '3', '8', '8', '4', '2', '3', '1', '5', '3', '9', '9', '1', '2', '6', '2', '1', '9', '3', '7', '7', '4', '6', '8', '8', '3', '1', '3', '7', '7', '7', '0', '3', '3', '1', '6', '9', '3', '3', '3', '8', '2', '0', '9', '9', '4', '9', '9', '0', '4', '7', '3', '4', '3', '3', '3', '6', '2', '2', '8', '4', '1', '8', '7', '9', '6', '8', '6', '1', '3', '7', '2', '5', '0', '9', '9', '4', '9', '1', '4', '9', '6', '4', '6', '7', '6', '1', '0', '3', '2', '5', '0', '5', '8', '9', '1', '3', '5', '7', '7', '9', '7', '9', '4', '6', '5', '8', '5', '4', '5', '1', '3', '9', '9', '7', '8', '3', '2', '9', '9', '6', '7', '8', '8', '5', '3', '9', '2', '2', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow093_jensenBoundDenominatorChars : List Char := ['6', '6', '0', '9', '3', '2', '4', '8', '2', '3', '4', '8', '7', '7', '2', '5', '4', '0', '2', '0', '9', '6', '1', '4', '7', '4', '2', '5', '5', '5', '9', '8', '9', '1', '8', '0', '5', '1', '4', '5', '8', '2', '1', '8', '0', '6', '0', '8', '7', '5', '5', '9', '2', '0', '8', '6', '0', '3', '4', '5', '7', '7', '1', '3', '8', '2', '4', '8', '3', '9', '8', '6', '2', '5', '6', '8', '4', '3', '4', '0', '0', '6', '1', '1', '9', '5', '4', '5', '0', '6', '5', '9', '9', '7', '2', '3', '4', '4', '0', '5', '7', '3', '8', '0', '1', '0', '1', '3', '3', '1', '5', '4', '7', '1', '8', '4', '7', '4', '8', '2', '6', '0', '0', '5', '8', '5', '5', '6', '1', '0', '8', '8', '7', '9', '5', '3', '9', '9', '4', '6', '5', '8', '9', '2', '4', '9', '2', '3', '8', '9', '3', '6', '8', '1', '5', '8', '4', '2', '3', '9', '1', '8', '1', '0', '3', '9', '9', '6', '9', '7', '7', '2', '1', '9', '8', '7', '5', '1', '8', '9', '8', '0', '0', '7', '2', '0', '3', '3', '4', '2', '7', '6', '5', '8', '8', '1', '3', '2', '5', '1', '0', '9', '8', '2', '6', '0', '5', '8', '6', '9', '2', '4', '0', '7', '5', '3', '4', '2', '4', '0', '8', '2', '8', '1', '9', '3', '0', '6', '8', '9', '1', '7', '4', '9', '1', '9', '3']
noncomputable def geometryRow093_jensenBoundText : String := String.ofList (geometryRow093_jensenBoundNumeratorChars ++ '/' :: geometryRow093_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_jensenBound_before_field"
  err.flush

theorem geometryRow093_jensenBound_field :
    geometryRowsJson093.getObjVal? "jensen_bound" = .ok (.str geometryRow093_jensenBoundText) := by rfl

theorem geometryRow093_jensenBound_numerator_no_slash :
    geometryRow093_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow093_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow093_jensenBoundNumeratorChars = some (72915582871907500628556520577806153324292640464189651025743791619746354461118323884231539912621937746883137770331693338209949904734333622841879686137250994914964676103250589135779794658545139978329967885392281600000000000000 : Int) := by decide +kernel

theorem geometryRow093_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow093_jensenBoundDenominatorChars = some (660932482348772540209614742555989180514582180608755920860345771382483986256843400611954506599723440573801013315471847482600585561088795399465892492389368158423918103996977219875189800720334276588132510982605869240753424082819306891749193 : Int) := by decide +kernel

theorem geometryRow093_jensenBound_denominator_nonzero : (660932482348772540209614742555989180514582180608755920860345771382483986256843400611954506599723440573801013315471847482600585561088795399465892492389368158423918103996977219875189800720334276588132510982605869240753424082819306891749193 : Int) ≠ 0 := by decide +kernel

theorem geometryRow093_jensenBound_parse :
    parseRational geometryRow093_jensenBoundText = .ok geometryRowsTyped093.jensenBound :=
  original_rational_fraction_of_chars geometryRow093_jensenBoundNumeratorChars geometryRow093_jensenBoundDenominatorChars
    (72915582871907500628556520577806153324292640464189651025743791619746354461118323884231539912621937746883137770331693338209949904734333622841879686137250994914964676103250589135779794658545139978329967885392281600000000000000 : Int) (660932482348772540209614742555989180514582180608755920860345771382483986256843400611954506599723440573801013315471847482600585561088795399465892492389368158423918103996977219875189800720334276588132510982605869240753424082819306891749193 : Int)
    geometryRow093_jensenBound_numerator_no_slash geometryRow093_jensenBound_numerator_parse
    geometryRow093_jensenBound_denominator_parse geometryRow093_jensenBound_denominator_nonzero

theorem geometryRow093_jensenBound_read :
    rationalField geometryRowsJson093 "jensen_bound" = .ok geometryRowsTyped093.jensenBound :=
  original_rationalField_of_string geometryRowsJson093 "jensen_bound" geometryRow093_jensenBoundText
    geometryRowsTyped093.jensenBound geometryRow093_jensenBound_field geometryRow093_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_factorMaxima_before"
  err.flush

theorem geometryRow093_factorMaxima_read :
    rationalArrayField geometryRowsJson093 "factor_maxima" = .ok geometryRowsTyped093.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_gapWeightedMeans_before"
  err.flush

theorem geometryRow093_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson093 "gap_weighted_means" = .ok geometryRowsTyped093.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow093_floorChars : List Char := ['8', '7', '4', '0', '6', '3', '2', '0', '6', '7', '3', '9', '0', '6', '6', '6']
noncomputable def geometryRow093_floorText : String := String.ofList geometryRow093_floorChars

theorem geometryRow093_floor_text_read :
    geometryRowsJson093.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow093_floorText := by rfl

theorem geometryRow093_floor_chars_parse :
    SourceJson.intChars geometryRow093_floorChars = some (8740632067390666 : Int) := by decide +kernel

theorem geometryRow093_floor_parse :
    parseInteger geometryRow093_floorText = .ok geometryRowsTyped093.jensenFloorQ96 := by
  simp only [geometryRow093_floorText, parseInteger, String.toList_ofList, geometryRow093_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_093 :
    decodeGeometryRow geometryRowsJson093 = .ok geometryRowsTyped093 :=
  original_geometryRow_of_fields geometryRowsJson093 geometryRowsTyped093 geometryRow093_floorText
    geometryRow093_simplexId_read geometryRow093_vertexIds_read
    geometryRow093_physicalVolume_read geometryRow093_meanGap_read
    geometryRow093_factorMaxima_read geometryRow093_gapWeightedMeans_read
    geometryRow093_jensenBound_read geometryRow093_floor_text_read geometryRow093_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_093_original_decoder_complete"
  err.flush

theorem geometryRow093_shape :
    geometryRowsTyped093.simplexId = 93 ∧
    geometryRowsTyped093.vertexIds.size = 9 ∧ geometryRowsTyped093.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped093.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped093.factorMaxima.size = 10 ∧ geometryRowsTyped093.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson094 : SourceJson :=
  (SimplicesBlock011.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped094 : GeometryRow :=
  { simplexId := 94,
    vertexIds := #[32, 30, 29, 20, 15, 13, 10, 1, 0],
    physicalVolume := ((2047478932850991745115757536406941121942954097 : ℚ) / (18278362790295552000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((1915281007994908080553 : ℚ) / (21754440104055120000000 : ℚ)), ((1399056963625955837663 : ℚ) / (15538885788610800000000 : ℚ)), ((123178514055132187133 : ℚ) / (1050939135461600000000 : ℚ)), ((19686370213719375102301 : ℚ) / (217544401040551200000000 : ℚ)), ((19209945128322810110537 : ℚ) / (217544401040551200000000 : ℚ)), ((32347370406762759499 : ℚ) / (439483638465760000000 : ℚ)), ((73835233785415553891 : ℚ) / (1977676373095920000000 : ℚ)), ((69474946266763179119 : ℚ) / (1977676373095920000000 : ℚ)), ((68400116418554894783 : ℚ) / (1977676373095920000000 : ℚ)), ((477142293294547898581 : ℚ) / (15538885788610800000000 : ℚ))],
    jensenBound := ((1724430969894290279259188174335554560536879041097901216563054851425455173405974721076399589905774942666499747187225341458662480775802651545262418665687172431748539684055731404800000000000000000 : ℚ) / (1982329590392027190195886792551899738288227692184039528795328253547327777634639323289927229852586216304508571354757833012087270473663556409636744731294294923341067561438534279129096244930997891174900253047 : ℚ)),
    jensenFloorQ96 := (68920676858986160 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_simplexId_before"
  err.flush

theorem geometryRow094_simplexId_read :
    geometryRowsJson094.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped094.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_vertexIds_before"
  err.flush

theorem geometryRow094_vertexIds_read :
    geometryRowsJson094.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped094.vertexIds := by decide +kernel

noncomputable def geometryRow094_physicalVolumeNumeratorChars : List Char := ['2', '0', '4', '7', '4', '7', '8', '9', '3', '2', '8', '5', '0', '9', '9', '1', '7', '4', '5', '1', '1', '5', '7', '5', '7', '5', '3', '6', '4', '0', '6', '9', '4', '1', '1', '2', '1', '9', '4', '2', '9', '5', '4', '0', '9', '7']
noncomputable def geometryRow094_physicalVolumeDenominatorChars : List Char := ['1', '8', '2', '7', '8', '3', '6', '2', '7', '9', '0', '2', '9', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow094_physicalVolumeText : String := String.ofList (geometryRow094_physicalVolumeNumeratorChars ++ '/' :: geometryRow094_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_physicalVolume_before_field"
  err.flush

theorem geometryRow094_physicalVolume_field :
    geometryRowsJson094.getObjVal? "physical_volume" = .ok (.str geometryRow094_physicalVolumeText) := by rfl

theorem geometryRow094_physicalVolume_numerator_no_slash :
    geometryRow094_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow094_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow094_physicalVolumeNumeratorChars = some (2047478932850991745115757536406941121942954097 : Int) := by decide +kernel

theorem geometryRow094_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow094_physicalVolumeDenominatorChars = some (18278362790295552000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow094_physicalVolume_denominator_nonzero : (18278362790295552000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow094_physicalVolume_parse :
    parseRational geometryRow094_physicalVolumeText = .ok geometryRowsTyped094.physicalVolume :=
  original_rational_fraction_of_chars geometryRow094_physicalVolumeNumeratorChars geometryRow094_physicalVolumeDenominatorChars
    (2047478932850991745115757536406941121942954097 : Int) (18278362790295552000000000000000000000000000000000000000000000000000 : Int)
    geometryRow094_physicalVolume_numerator_no_slash geometryRow094_physicalVolume_numerator_parse
    geometryRow094_physicalVolume_denominator_parse geometryRow094_physicalVolume_denominator_nonzero

theorem geometryRow094_physicalVolume_read :
    rationalField geometryRowsJson094 "physical_volume" = .ok geometryRowsTyped094.physicalVolume :=
  original_rationalField_of_string geometryRowsJson094 "physical_volume" geometryRow094_physicalVolumeText
    geometryRowsTyped094.physicalVolume geometryRow094_physicalVolume_field geometryRow094_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_physicalVolume_complete"
  err.flush

noncomputable def geometryRow094_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow094_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow094_meanGapText : String := String.ofList (geometryRow094_meanGapNumeratorChars ++ '/' :: geometryRow094_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_meanGap_before_field"
  err.flush

theorem geometryRow094_meanGap_field :
    geometryRowsJson094.getObjVal? "mean_gap" = .ok (.str geometryRow094_meanGapText) := by rfl

theorem geometryRow094_meanGap_numerator_no_slash :
    geometryRow094_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow094_meanGap_numerator_parse :
    SourceJson.intChars geometryRow094_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow094_meanGap_denominator_parse :
    SourceJson.intChars geometryRow094_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow094_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow094_meanGap_parse :
    parseRational geometryRow094_meanGapText = .ok geometryRowsTyped094.meanGap :=
  original_rational_fraction_of_chars geometryRow094_meanGapNumeratorChars geometryRow094_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow094_meanGap_numerator_no_slash geometryRow094_meanGap_numerator_parse
    geometryRow094_meanGap_denominator_parse geometryRow094_meanGap_denominator_nonzero

theorem geometryRow094_meanGap_read :
    rationalField geometryRowsJson094 "mean_gap" = .ok geometryRowsTyped094.meanGap :=
  original_rationalField_of_string geometryRowsJson094 "mean_gap" geometryRow094_meanGapText
    geometryRowsTyped094.meanGap geometryRow094_meanGap_field geometryRow094_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_meanGap_complete"
  err.flush

noncomputable def geometryRow094_jensenBoundNumeratorChars : List Char := ['1', '7', '2', '4', '4', '3', '0', '9', '6', '9', '8', '9', '4', '2', '9', '0', '2', '7', '9', '2', '5', '9', '1', '8', '8', '1', '7', '4', '3', '3', '5', '5', '5', '4', '5', '6', '0', '5', '3', '6', '8', '7', '9', '0', '4', '1', '0', '9', '7', '9', '0', '1', '2', '1', '6', '5', '6', '3', '0', '5', '4', '8', '5', '1', '4', '2', '5', '4', '5', '5', '1', '7', '3', '4', '0', '5', '9', '7', '4', '7', '2', '1', '0', '7', '6', '3', '9', '9', '5', '8', '9', '9', '0', '5', '7', '7', '4', '9', '4', '2', '6', '6', '6', '4', '9', '9', '7', '4', '7', '1', '8', '7', '2', '2', '5', '3', '4', '1', '4', '5', '8', '6', '6', '2', '4', '8', '0', '7', '7', '5', '8', '0', '2', '6', '5', '1', '5', '4', '5', '2', '6', '2', '4', '1', '8', '6', '6', '5', '6', '8', '7', '1', '7', '2', '4', '3', '1', '7', '4', '8', '5', '3', '9', '6', '8', '4', '0', '5', '5', '7', '3', '1', '4', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow094_jensenBoundDenominatorChars : List Char := ['1', '9', '8', '2', '3', '2', '9', '5', '9', '0', '3', '9', '2', '0', '2', '7', '1', '9', '0', '1', '9', '5', '8', '8', '6', '7', '9', '2', '5', '5', '1', '8', '9', '9', '7', '3', '8', '2', '8', '8', '2', '2', '7', '6', '9', '2', '1', '8', '4', '0', '3', '9', '5', '2', '8', '7', '9', '5', '3', '2', '8', '2', '5', '3', '5', '4', '7', '3', '2', '7', '7', '7', '7', '6', '3', '4', '6', '3', '9', '3', '2', '3', '2', '8', '9', '9', '2', '7', '2', '2', '9', '8', '5', '2', '5', '8', '6', '2', '1', '6', '3', '0', '4', '5', '0', '8', '5', '7', '1', '3', '5', '4', '7', '5', '7', '8', '3', '3', '0', '1', '2', '0', '8', '7', '2', '7', '0', '4', '7', '3', '6', '6', '3', '5', '5', '6', '4', '0', '9', '6', '3', '6', '7', '4', '4', '7', '3', '1', '2', '9', '4', '2', '9', '4', '9', '2', '3', '3', '4', '1', '0', '6', '7', '5', '6', '1', '4', '3', '8', '5', '3', '4', '2', '7', '9', '1', '2', '9', '0', '9', '6', '2', '4', '4', '9', '3', '0', '9', '9', '7', '8', '9', '1', '1', '7', '4', '9', '0', '0', '2', '5', '3', '0', '4', '7']
noncomputable def geometryRow094_jensenBoundText : String := String.ofList (geometryRow094_jensenBoundNumeratorChars ++ '/' :: geometryRow094_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_jensenBound_before_field"
  err.flush

theorem geometryRow094_jensenBound_field :
    geometryRowsJson094.getObjVal? "jensen_bound" = .ok (.str geometryRow094_jensenBoundText) := by rfl

theorem geometryRow094_jensenBound_numerator_no_slash :
    geometryRow094_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow094_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow094_jensenBoundNumeratorChars = some (1724430969894290279259188174335554560536879041097901216563054851425455173405974721076399589905774942666499747187225341458662480775802651545262418665687172431748539684055731404800000000000000000 : Int) := by decide +kernel

theorem geometryRow094_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow094_jensenBoundDenominatorChars = some (1982329590392027190195886792551899738288227692184039528795328253547327777634639323289927229852586216304508571354757833012087270473663556409636744731294294923341067561438534279129096244930997891174900253047 : Int) := by decide +kernel

theorem geometryRow094_jensenBound_denominator_nonzero : (1982329590392027190195886792551899738288227692184039528795328253547327777634639323289927229852586216304508571354757833012087270473663556409636744731294294923341067561438534279129096244930997891174900253047 : Int) ≠ 0 := by decide +kernel

theorem geometryRow094_jensenBound_parse :
    parseRational geometryRow094_jensenBoundText = .ok geometryRowsTyped094.jensenBound :=
  original_rational_fraction_of_chars geometryRow094_jensenBoundNumeratorChars geometryRow094_jensenBoundDenominatorChars
    (1724430969894290279259188174335554560536879041097901216563054851425455173405974721076399589905774942666499747187225341458662480775802651545262418665687172431748539684055731404800000000000000000 : Int) (1982329590392027190195886792551899738288227692184039528795328253547327777634639323289927229852586216304508571354757833012087270473663556409636744731294294923341067561438534279129096244930997891174900253047 : Int)
    geometryRow094_jensenBound_numerator_no_slash geometryRow094_jensenBound_numerator_parse
    geometryRow094_jensenBound_denominator_parse geometryRow094_jensenBound_denominator_nonzero

theorem geometryRow094_jensenBound_read :
    rationalField geometryRowsJson094 "jensen_bound" = .ok geometryRowsTyped094.jensenBound :=
  original_rationalField_of_string geometryRowsJson094 "jensen_bound" geometryRow094_jensenBoundText
    geometryRowsTyped094.jensenBound geometryRow094_jensenBound_field geometryRow094_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_factorMaxima_before"
  err.flush

theorem geometryRow094_factorMaxima_read :
    rationalArrayField geometryRowsJson094 "factor_maxima" = .ok geometryRowsTyped094.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_gapWeightedMeans_before"
  err.flush

theorem geometryRow094_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson094 "gap_weighted_means" = .ok geometryRowsTyped094.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow094_floorChars : List Char := ['6', '8', '9', '2', '0', '6', '7', '6', '8', '5', '8', '9', '8', '6', '1', '6', '0']
noncomputable def geometryRow094_floorText : String := String.ofList geometryRow094_floorChars

theorem geometryRow094_floor_text_read :
    geometryRowsJson094.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow094_floorText := by rfl

theorem geometryRow094_floor_chars_parse :
    SourceJson.intChars geometryRow094_floorChars = some (68920676858986160 : Int) := by decide +kernel

theorem geometryRow094_floor_parse :
    parseInteger geometryRow094_floorText = .ok geometryRowsTyped094.jensenFloorQ96 := by
  simp only [geometryRow094_floorText, parseInteger, String.toList_ofList, geometryRow094_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_094 :
    decodeGeometryRow geometryRowsJson094 = .ok geometryRowsTyped094 :=
  original_geometryRow_of_fields geometryRowsJson094 geometryRowsTyped094 geometryRow094_floorText
    geometryRow094_simplexId_read geometryRow094_vertexIds_read
    geometryRow094_physicalVolume_read geometryRow094_meanGap_read
    geometryRow094_factorMaxima_read geometryRow094_gapWeightedMeans_read
    geometryRow094_jensenBound_read geometryRow094_floor_text_read geometryRow094_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_094_original_decoder_complete"
  err.flush

theorem geometryRow094_shape :
    geometryRowsTyped094.simplexId = 94 ∧
    geometryRowsTyped094.vertexIds.size = 9 ∧ geometryRowsTyped094.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped094.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped094.factorMaxima.size = 10 ∧ geometryRowsTyped094.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson095 : SourceJson :=
  (SimplicesBlock011.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped095 : GeometryRow :=
  { simplexId := 95,
    vertexIds := #[32, 30, 29, 20, 15, 13, 10, 8, 0],
    physicalVolume := ((45308323438911221983465913969389114619641057117 : ℚ) / (40287003701059584000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((1893461562599 : ℚ) / (21677040000000 : ℚ)), ((9610463083687 : ℚ) / (108385200000000 : ℚ)), ((3320255375377 : ℚ) / (28274400000000 : ℚ)), ((58412544873961 : ℚ) / (650311200000000 : ℚ)), ((56988354834997 : ℚ) / (650311200000000 : ℚ)), ((883592022583 : ℚ) / (11823840000000 : ℚ)), ((31900475941 : ℚ) / (844560000000 : ℚ)), ((211757767069 : ℚ) / (5911920000000 : ℚ)), ((208544749933 : ℚ) / (5911920000000 : ℚ)), ((9836246315207 : ℚ) / (325155600000000 : ℚ))],
    jensenBound := ((10524005938866198426088759220751833617482299175622273232866294767255476923938635020029085758259200000000000000000 : ℚ) / (2462529820300654520555349281710913474506358346861159756697992862925075176743319014610630852555219641016633060044186027986089 : ℚ)),
    jensenFloorQ96 := (338593931310758467 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_simplexId_before"
  err.flush

theorem geometryRow095_simplexId_read :
    geometryRowsJson095.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped095.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_vertexIds_before"
  err.flush

theorem geometryRow095_vertexIds_read :
    geometryRowsJson095.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped095.vertexIds := by decide +kernel

noncomputable def geometryRow095_physicalVolumeNumeratorChars : List Char := ['4', '5', '3', '0', '8', '3', '2', '3', '4', '3', '8', '9', '1', '1', '2', '2', '1', '9', '8', '3', '4', '6', '5', '9', '1', '3', '9', '6', '9', '3', '8', '9', '1', '1', '4', '6', '1', '9', '6', '4', '1', '0', '5', '7', '1', '1', '7']
noncomputable def geometryRow095_physicalVolumeDenominatorChars : List Char := ['4', '0', '2', '8', '7', '0', '0', '3', '7', '0', '1', '0', '5', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow095_physicalVolumeText : String := String.ofList (geometryRow095_physicalVolumeNumeratorChars ++ '/' :: geometryRow095_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_physicalVolume_before_field"
  err.flush

theorem geometryRow095_physicalVolume_field :
    geometryRowsJson095.getObjVal? "physical_volume" = .ok (.str geometryRow095_physicalVolumeText) := by rfl

theorem geometryRow095_physicalVolume_numerator_no_slash :
    geometryRow095_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow095_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow095_physicalVolumeNumeratorChars = some (45308323438911221983465913969389114619641057117 : Int) := by decide +kernel

theorem geometryRow095_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow095_physicalVolumeDenominatorChars = some (40287003701059584000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow095_physicalVolume_denominator_nonzero : (40287003701059584000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow095_physicalVolume_parse :
    parseRational geometryRow095_physicalVolumeText = .ok geometryRowsTyped095.physicalVolume :=
  original_rational_fraction_of_chars geometryRow095_physicalVolumeNumeratorChars geometryRow095_physicalVolumeDenominatorChars
    (45308323438911221983465913969389114619641057117 : Int) (40287003701059584000000000000000000000000000000000000000000000000000 : Int)
    geometryRow095_physicalVolume_numerator_no_slash geometryRow095_physicalVolume_numerator_parse
    geometryRow095_physicalVolume_denominator_parse geometryRow095_physicalVolume_denominator_nonzero

theorem geometryRow095_physicalVolume_read :
    rationalField geometryRowsJson095 "physical_volume" = .ok geometryRowsTyped095.physicalVolume :=
  original_rationalField_of_string geometryRowsJson095 "physical_volume" geometryRow095_physicalVolumeText
    geometryRowsTyped095.physicalVolume geometryRow095_physicalVolume_field geometryRow095_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_physicalVolume_complete"
  err.flush

noncomputable def geometryRow095_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow095_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow095_meanGapText : String := String.ofList (geometryRow095_meanGapNumeratorChars ++ '/' :: geometryRow095_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_meanGap_before_field"
  err.flush

theorem geometryRow095_meanGap_field :
    geometryRowsJson095.getObjVal? "mean_gap" = .ok (.str geometryRow095_meanGapText) := by rfl

theorem geometryRow095_meanGap_numerator_no_slash :
    geometryRow095_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow095_meanGap_numerator_parse :
    SourceJson.intChars geometryRow095_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow095_meanGap_denominator_parse :
    SourceJson.intChars geometryRow095_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow095_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow095_meanGap_parse :
    parseRational geometryRow095_meanGapText = .ok geometryRowsTyped095.meanGap :=
  original_rational_fraction_of_chars geometryRow095_meanGapNumeratorChars geometryRow095_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow095_meanGap_numerator_no_slash geometryRow095_meanGap_numerator_parse
    geometryRow095_meanGap_denominator_parse geometryRow095_meanGap_denominator_nonzero

theorem geometryRow095_meanGap_read :
    rationalField geometryRowsJson095 "mean_gap" = .ok geometryRowsTyped095.meanGap :=
  original_rationalField_of_string geometryRowsJson095 "mean_gap" geometryRow095_meanGapText
    geometryRowsTyped095.meanGap geometryRow095_meanGap_field geometryRow095_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_meanGap_complete"
  err.flush

noncomputable def geometryRow095_jensenBoundNumeratorChars : List Char := ['1', '0', '5', '2', '4', '0', '0', '5', '9', '3', '8', '8', '6', '6', '1', '9', '8', '4', '2', '6', '0', '8', '8', '7', '5', '9', '2', '2', '0', '7', '5', '1', '8', '3', '3', '6', '1', '7', '4', '8', '2', '2', '9', '9', '1', '7', '5', '6', '2', '2', '2', '7', '3', '2', '3', '2', '8', '6', '6', '2', '9', '4', '7', '6', '7', '2', '5', '5', '4', '7', '6', '9', '2', '3', '9', '3', '8', '6', '3', '5', '0', '2', '0', '0', '2', '9', '0', '8', '5', '7', '5', '8', '2', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow095_jensenBoundDenominatorChars : List Char := ['2', '4', '6', '2', '5', '2', '9', '8', '2', '0', '3', '0', '0', '6', '5', '4', '5', '2', '0', '5', '5', '5', '3', '4', '9', '2', '8', '1', '7', '1', '0', '9', '1', '3', '4', '7', '4', '5', '0', '6', '3', '5', '8', '3', '4', '6', '8', '6', '1', '1', '5', '9', '7', '5', '6', '6', '9', '7', '9', '9', '2', '8', '6', '2', '9', '2', '5', '0', '7', '5', '1', '7', '6', '7', '4', '3', '3', '1', '9', '0', '1', '4', '6', '1', '0', '6', '3', '0', '8', '5', '2', '5', '5', '5', '2', '1', '9', '6', '4', '1', '0', '1', '6', '6', '3', '3', '0', '6', '0', '0', '4', '4', '1', '8', '6', '0', '2', '7', '9', '8', '6', '0', '8', '9']
noncomputable def geometryRow095_jensenBoundText : String := String.ofList (geometryRow095_jensenBoundNumeratorChars ++ '/' :: geometryRow095_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_jensenBound_before_field"
  err.flush

theorem geometryRow095_jensenBound_field :
    geometryRowsJson095.getObjVal? "jensen_bound" = .ok (.str geometryRow095_jensenBoundText) := by rfl

theorem geometryRow095_jensenBound_numerator_no_slash :
    geometryRow095_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow095_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow095_jensenBoundNumeratorChars = some (10524005938866198426088759220751833617482299175622273232866294767255476923938635020029085758259200000000000000000 : Int) := by decide +kernel

theorem geometryRow095_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow095_jensenBoundDenominatorChars = some (2462529820300654520555349281710913474506358346861159756697992862925075176743319014610630852555219641016633060044186027986089 : Int) := by decide +kernel

theorem geometryRow095_jensenBound_denominator_nonzero : (2462529820300654520555349281710913474506358346861159756697992862925075176743319014610630852555219641016633060044186027986089 : Int) ≠ 0 := by decide +kernel

theorem geometryRow095_jensenBound_parse :
    parseRational geometryRow095_jensenBoundText = .ok geometryRowsTyped095.jensenBound :=
  original_rational_fraction_of_chars geometryRow095_jensenBoundNumeratorChars geometryRow095_jensenBoundDenominatorChars
    (10524005938866198426088759220751833617482299175622273232866294767255476923938635020029085758259200000000000000000 : Int) (2462529820300654520555349281710913474506358346861159756697992862925075176743319014610630852555219641016633060044186027986089 : Int)
    geometryRow095_jensenBound_numerator_no_slash geometryRow095_jensenBound_numerator_parse
    geometryRow095_jensenBound_denominator_parse geometryRow095_jensenBound_denominator_nonzero

theorem geometryRow095_jensenBound_read :
    rationalField geometryRowsJson095 "jensen_bound" = .ok geometryRowsTyped095.jensenBound :=
  original_rationalField_of_string geometryRowsJson095 "jensen_bound" geometryRow095_jensenBoundText
    geometryRowsTyped095.jensenBound geometryRow095_jensenBound_field geometryRow095_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_factorMaxima_before"
  err.flush

theorem geometryRow095_factorMaxima_read :
    rationalArrayField geometryRowsJson095 "factor_maxima" = .ok geometryRowsTyped095.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_gapWeightedMeans_before"
  err.flush

theorem geometryRow095_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson095 "gap_weighted_means" = .ok geometryRowsTyped095.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow095_floorChars : List Char := ['3', '3', '8', '5', '9', '3', '9', '3', '1', '3', '1', '0', '7', '5', '8', '4', '6', '7']
noncomputable def geometryRow095_floorText : String := String.ofList geometryRow095_floorChars

theorem geometryRow095_floor_text_read :
    geometryRowsJson095.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow095_floorText := by rfl

theorem geometryRow095_floor_chars_parse :
    SourceJson.intChars geometryRow095_floorChars = some (338593931310758467 : Int) := by decide +kernel

theorem geometryRow095_floor_parse :
    parseInteger geometryRow095_floorText = .ok geometryRowsTyped095.jensenFloorQ96 := by
  simp only [geometryRow095_floorText, parseInteger, String.toList_ofList, geometryRow095_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_095 :
    decodeGeometryRow geometryRowsJson095 = .ok geometryRowsTyped095 :=
  original_geometryRow_of_fields geometryRowsJson095 geometryRowsTyped095 geometryRow095_floorText
    geometryRow095_simplexId_read geometryRow095_vertexIds_read
    geometryRow095_physicalVolume_read geometryRow095_meanGap_read
    geometryRow095_factorMaxima_read geometryRow095_gapWeightedMeans_read
    geometryRow095_jensenBound_read geometryRow095_floor_text_read geometryRow095_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_095_original_decoder_complete"
  err.flush

theorem geometryRow095_shape :
    geometryRowsTyped095.simplexId = 95 ∧
    geometryRowsTyped095.vertexIds.size = 9 ∧ geometryRowsTyped095.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped095.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped095.factorMaxima.size = 10 ∧ geometryRowsTyped095.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock011 : List SourceJson := [geometryRowsJson088, geometryRowsJson089, geometryRowsJson090, geometryRowsJson091, geometryRowsJson092, geometryRowsJson093, geometryRowsJson094, geometryRowsJson095]
noncomputable def geometryRowsTypedBlock011 : List GeometryRow := [geometryRowsTyped088, geometryRowsTyped089, geometryRowsTyped090, geometryRowsTyped091, geometryRowsTyped092, geometryRowsTyped093, geometryRowsTyped094, geometryRowsTyped095]

theorem geometry_Rows_block_011_push_eq (acc : List SourceJson) :
    SimplicesBlock011.blockPush acc = [geometryRowsJson095, geometryRowsJson094, geometryRowsJson093, geometryRowsJson092, geometryRowsJson091, geometryRowsJson090, geometryRowsJson089, geometryRowsJson088] ++ acc := by rfl

theorem geometry_Rows_block_011_reverse (acc : List SourceJson) :
    (SimplicesBlock011.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock011 := by
  rw [geometry_Rows_block_011_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_011 :
    geometryRowsJsonBlock011.mapM decodeGeometryRow = .ok geometryRowsTypedBlock011 := by
  simp only [geometryRowsJsonBlock011, geometryRowsTypedBlock011, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_088, decode_geometry_Rows_089, decode_geometry_Rows_090, decode_geometry_Rows_091, decode_geometry_Rows_092, decode_geometry_Rows_093, decode_geometry_Rows_094, decode_geometry_Rows_095]
  rfl

theorem geometry_Rows_block_011_length : geometryRowsTypedBlock011.length = 8 := by rfl

#print axioms geometryRow088_simplexId_read
#print axioms geometryRow088_vertexIds_read
#print axioms geometryRow088_physicalVolume_field
#print axioms geometryRow088_physicalVolume_numerator_no_slash
#print axioms geometryRow088_physicalVolume_numerator_parse
#print axioms geometryRow088_physicalVolume_denominator_parse
#print axioms geometryRow088_physicalVolume_denominator_nonzero
#print axioms geometryRow088_physicalVolume_parse
#print axioms geometryRow088_physicalVolume_read
#print axioms geometryRow088_meanGap_field
#print axioms geometryRow088_meanGap_numerator_no_slash
#print axioms geometryRow088_meanGap_numerator_parse
#print axioms geometryRow088_meanGap_denominator_parse
#print axioms geometryRow088_meanGap_denominator_nonzero
#print axioms geometryRow088_meanGap_parse
#print axioms geometryRow088_meanGap_read
#print axioms geometryRow088_jensenBound_field
#print axioms geometryRow088_jensenBound_numerator_no_slash
#print axioms geometryRow088_jensenBound_numerator_parse
#print axioms geometryRow088_jensenBound_denominator_parse
#print axioms geometryRow088_jensenBound_denominator_nonzero
#print axioms geometryRow088_jensenBound_parse
#print axioms geometryRow088_jensenBound_read
#print axioms geometryRow088_factorMaxima_read
#print axioms geometryRow088_gapWeightedMeans_read
#print axioms geometryRow088_floor_text_read
#print axioms geometryRow088_floor_chars_parse
#print axioms geometryRow088_floor_parse
#print axioms decode_geometry_Rows_088
#print axioms geometryRow088_shape
#print axioms geometryRow089_simplexId_read
#print axioms geometryRow089_vertexIds_read
#print axioms geometryRow089_physicalVolume_field
#print axioms geometryRow089_physicalVolume_numerator_no_slash
#print axioms geometryRow089_physicalVolume_numerator_parse
#print axioms geometryRow089_physicalVolume_denominator_parse
#print axioms geometryRow089_physicalVolume_denominator_nonzero
#print axioms geometryRow089_physicalVolume_parse
#print axioms geometryRow089_physicalVolume_read
#print axioms geometryRow089_meanGap_field
#print axioms geometryRow089_meanGap_numerator_no_slash
#print axioms geometryRow089_meanGap_numerator_parse
#print axioms geometryRow089_meanGap_denominator_parse
#print axioms geometryRow089_meanGap_denominator_nonzero
#print axioms geometryRow089_meanGap_parse
#print axioms geometryRow089_meanGap_read
#print axioms geometryRow089_jensenBound_field
#print axioms geometryRow089_jensenBound_numerator_no_slash
#print axioms geometryRow089_jensenBound_numerator_parse
#print axioms geometryRow089_jensenBound_denominator_parse
#print axioms geometryRow089_jensenBound_denominator_nonzero
#print axioms geometryRow089_jensenBound_parse
#print axioms geometryRow089_jensenBound_read
#print axioms geometryRow089_factorMaxima_read
#print axioms geometryRow089_gapWeightedMeans_read
#print axioms geometryRow089_floor_text_read
#print axioms geometryRow089_floor_chars_parse
#print axioms geometryRow089_floor_parse
#print axioms decode_geometry_Rows_089
#print axioms geometryRow089_shape
#print axioms geometryRow090_simplexId_read
#print axioms geometryRow090_vertexIds_read
#print axioms geometryRow090_physicalVolume_field
#print axioms geometryRow090_physicalVolume_numerator_no_slash
#print axioms geometryRow090_physicalVolume_numerator_parse
#print axioms geometryRow090_physicalVolume_denominator_parse
#print axioms geometryRow090_physicalVolume_denominator_nonzero
#print axioms geometryRow090_physicalVolume_parse
#print axioms geometryRow090_physicalVolume_read
#print axioms geometryRow090_meanGap_field
#print axioms geometryRow090_meanGap_numerator_no_slash
#print axioms geometryRow090_meanGap_numerator_parse
#print axioms geometryRow090_meanGap_denominator_parse
#print axioms geometryRow090_meanGap_denominator_nonzero
#print axioms geometryRow090_meanGap_parse
#print axioms geometryRow090_meanGap_read
#print axioms geometryRow090_jensenBound_field
#print axioms geometryRow090_jensenBound_numerator_no_slash
#print axioms geometryRow090_jensenBound_numerator_parse
#print axioms geometryRow090_jensenBound_denominator_parse
#print axioms geometryRow090_jensenBound_denominator_nonzero
#print axioms geometryRow090_jensenBound_parse
#print axioms geometryRow090_jensenBound_read
#print axioms geometryRow090_factorMaxima_read
#print axioms geometryRow090_gapWeightedMeans_read
#print axioms geometryRow090_floor_text_read
#print axioms geometryRow090_floor_chars_parse
#print axioms geometryRow090_floor_parse
#print axioms decode_geometry_Rows_090
#print axioms geometryRow090_shape
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
#print axioms geometryRow091_shape
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
#print axioms geometryRow092_shape
#print axioms geometryRow093_simplexId_read
#print axioms geometryRow093_vertexIds_read
#print axioms geometryRow093_physicalVolume_field
#print axioms geometryRow093_physicalVolume_numerator_no_slash
#print axioms geometryRow093_physicalVolume_numerator_parse
#print axioms geometryRow093_physicalVolume_denominator_parse
#print axioms geometryRow093_physicalVolume_denominator_nonzero
#print axioms geometryRow093_physicalVolume_parse
#print axioms geometryRow093_physicalVolume_read
#print axioms geometryRow093_meanGap_field
#print axioms geometryRow093_meanGap_numerator_no_slash
#print axioms geometryRow093_meanGap_numerator_parse
#print axioms geometryRow093_meanGap_denominator_parse
#print axioms geometryRow093_meanGap_denominator_nonzero
#print axioms geometryRow093_meanGap_parse
#print axioms geometryRow093_meanGap_read
#print axioms geometryRow093_jensenBound_field
#print axioms geometryRow093_jensenBound_numerator_no_slash
#print axioms geometryRow093_jensenBound_numerator_parse
#print axioms geometryRow093_jensenBound_denominator_parse
#print axioms geometryRow093_jensenBound_denominator_nonzero
#print axioms geometryRow093_jensenBound_parse
#print axioms geometryRow093_jensenBound_read
#print axioms geometryRow093_factorMaxima_read
#print axioms geometryRow093_gapWeightedMeans_read
#print axioms geometryRow093_floor_text_read
#print axioms geometryRow093_floor_chars_parse
#print axioms geometryRow093_floor_parse
#print axioms decode_geometry_Rows_093
#print axioms geometryRow093_shape
#print axioms geometryRow094_simplexId_read
#print axioms geometryRow094_vertexIds_read
#print axioms geometryRow094_physicalVolume_field
#print axioms geometryRow094_physicalVolume_numerator_no_slash
#print axioms geometryRow094_physicalVolume_numerator_parse
#print axioms geometryRow094_physicalVolume_denominator_parse
#print axioms geometryRow094_physicalVolume_denominator_nonzero
#print axioms geometryRow094_physicalVolume_parse
#print axioms geometryRow094_physicalVolume_read
#print axioms geometryRow094_meanGap_field
#print axioms geometryRow094_meanGap_numerator_no_slash
#print axioms geometryRow094_meanGap_numerator_parse
#print axioms geometryRow094_meanGap_denominator_parse
#print axioms geometryRow094_meanGap_denominator_nonzero
#print axioms geometryRow094_meanGap_parse
#print axioms geometryRow094_meanGap_read
#print axioms geometryRow094_jensenBound_field
#print axioms geometryRow094_jensenBound_numerator_no_slash
#print axioms geometryRow094_jensenBound_numerator_parse
#print axioms geometryRow094_jensenBound_denominator_parse
#print axioms geometryRow094_jensenBound_denominator_nonzero
#print axioms geometryRow094_jensenBound_parse
#print axioms geometryRow094_jensenBound_read
#print axioms geometryRow094_factorMaxima_read
#print axioms geometryRow094_gapWeightedMeans_read
#print axioms geometryRow094_floor_text_read
#print axioms geometryRow094_floor_chars_parse
#print axioms geometryRow094_floor_parse
#print axioms decode_geometry_Rows_094
#print axioms geometryRow094_shape
#print axioms geometryRow095_simplexId_read
#print axioms geometryRow095_vertexIds_read
#print axioms geometryRow095_physicalVolume_field
#print axioms geometryRow095_physicalVolume_numerator_no_slash
#print axioms geometryRow095_physicalVolume_numerator_parse
#print axioms geometryRow095_physicalVolume_denominator_parse
#print axioms geometryRow095_physicalVolume_denominator_nonzero
#print axioms geometryRow095_physicalVolume_parse
#print axioms geometryRow095_physicalVolume_read
#print axioms geometryRow095_meanGap_field
#print axioms geometryRow095_meanGap_numerator_no_slash
#print axioms geometryRow095_meanGap_numerator_parse
#print axioms geometryRow095_meanGap_denominator_parse
#print axioms geometryRow095_meanGap_denominator_nonzero
#print axioms geometryRow095_meanGap_parse
#print axioms geometryRow095_meanGap_read
#print axioms geometryRow095_jensenBound_field
#print axioms geometryRow095_jensenBound_numerator_no_slash
#print axioms geometryRow095_jensenBound_numerator_parse
#print axioms geometryRow095_jensenBound_denominator_parse
#print axioms geometryRow095_jensenBound_denominator_nonzero
#print axioms geometryRow095_jensenBound_parse
#print axioms geometryRow095_jensenBound_read
#print axioms geometryRow095_factorMaxima_read
#print axioms geometryRow095_gapWeightedMeans_read
#print axioms geometryRow095_floor_text_read
#print axioms geometryRow095_floor_chars_parse
#print axioms geometryRow095_floor_parse
#print axioms decode_geometry_Rows_095
#print axioms geometryRow095_shape
#print axioms geometry_Rows_block_011_push_eq
#print axioms geometry_Rows_block_011_reverse
#print axioms decode_geometry_Rows_block_011
#print axioms geometry_Rows_block_011_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
