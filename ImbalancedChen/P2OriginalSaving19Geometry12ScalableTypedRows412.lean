import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry12ScalableSimplicesBlock412

/-! Local typed certificates for original cell 12, rows 3296 through 3303.
This owner imports only its own original parser leaf.  No cumulative typed
prefix, whole-array parser value, or completed geometric archive is imported.
The original rational decoder and GeometryRow record fields are unchanged. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry12ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry12ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson3296 : SourceJson :=
  (SimplicesBlock412.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped3296 : GeometryRow :=
  { simplexId := 3296,
    vertexIds := #[139, 133, 114, 113, 99, 62, 57, 52, 40],
    physicalVolume := ((128997816942369887710052559807725938289 : ℚ) / (39744380743200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1519241 : ℚ) / (1329750000 : ℚ)),
    factorMaxima := #[((621087 : ℚ) / (11875000 : ℚ)), ((621087 : ℚ) / (11875000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((3500143 : ℚ) / (47500000 : ℚ)), ((1187489 : ℚ) / (17000000 : ℚ)), ((1187489 : ℚ) / (17000000 : ℚ)), ((11 : ℚ) / (336 : ℚ)), ((11 : ℚ) / (336 : ℚ))],
    gapWeightedMeans := #[((33773384184870812707 : ℚ) / (913539287470950000000 : ℚ)), ((35182483434040700017 : ℚ) / (913539287470950000000 : ℚ)), ((16022173841836798791 : ℚ) / (135339153699400000000 : ℚ)), ((118954962660282055289 : ℚ) / (1218052383294600000000 : ℚ)), ((109344460345689474629 : ℚ) / (1218052383294600000000 : ℚ)), ((9362945880707975131 : ℚ) / (135339153699400000000 : ℚ)), ((81840236061737425451 : ℚ) / (1218052383294600000000 : ℚ)), ((9802825722126694037 : ℚ) / (152256547911825000000 : ℚ)), ((4829260967874425533 : ℚ) / (182707857494190000000 : ℚ)), ((2900463601880208919 : ℚ) / (121805238329460000000 : ℚ))],
    jensenBound := ((65011192338053797888259707712538555067168593964035242578267371422020761737425872449425487887788372622357920255755734119964335140987789161972594471138320000000000000000000000 : ℚ) / (1219964033074636575668455681057006413044865817829468327311633420284189700925754200960283701789144135952675860842155546801089006376922333083514496740648658685978295697723111172785512796447 : ℚ)),
    jensenFloorQ96 := (4222023905757478 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_simplexId_before"
  err.flush

theorem geometryRow3296_simplexId_read :
    geometryRowsJson3296.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped3296.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_vertexIds_before"
  err.flush

theorem geometryRow3296_vertexIds_read :
    geometryRowsJson3296.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped3296.vertexIds := by decide +kernel

noncomputable def geometryRow3296_physicalVolumeNumeratorChars : List Char := ['1', '2', '8', '9', '9', '7', '8', '1', '6', '9', '4', '2', '3', '6', '9', '8', '8', '7', '7', '1', '0', '0', '5', '2', '5', '5', '9', '8', '0', '7', '7', '2', '5', '9', '3', '8', '2', '8', '9']
noncomputable def geometryRow3296_physicalVolumeDenominatorChars : List Char := ['3', '9', '7', '4', '4', '3', '8', '0', '7', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3296_physicalVolumeText : String := String.ofList (geometryRow3296_physicalVolumeNumeratorChars ++ '/' :: geometryRow3296_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_physicalVolume_before_field"
  err.flush

theorem geometryRow3296_physicalVolume_field :
    geometryRowsJson3296.getObjVal? "physical_volume" = .ok (.str geometryRow3296_physicalVolumeText) := by rfl

theorem geometryRow3296_physicalVolume_numerator_no_slash :
    geometryRow3296_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3296_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow3296_physicalVolumeNumeratorChars = some (128997816942369887710052559807725938289 : Int) := by decide +kernel

theorem geometryRow3296_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow3296_physicalVolumeDenominatorChars = some (39744380743200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow3296_physicalVolume_denominator_nonzero : (39744380743200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3296_physicalVolume_parse :
    parseRational geometryRow3296_physicalVolumeText = .ok geometryRowsTyped3296.physicalVolume :=
  original_rational_fraction_of_chars geometryRow3296_physicalVolumeNumeratorChars geometryRow3296_physicalVolumeDenominatorChars
    (128997816942369887710052559807725938289 : Int) (39744380743200000000000000000000000000000000000000000000000000 : Int)
    geometryRow3296_physicalVolume_numerator_no_slash geometryRow3296_physicalVolume_numerator_parse
    geometryRow3296_physicalVolume_denominator_parse geometryRow3296_physicalVolume_denominator_nonzero

theorem geometryRow3296_physicalVolume_read :
    rationalField geometryRowsJson3296 "physical_volume" = .ok geometryRowsTyped3296.physicalVolume :=
  original_rationalField_of_string geometryRowsJson3296 "physical_volume" geometryRow3296_physicalVolumeText
    geometryRowsTyped3296.physicalVolume geometryRow3296_physicalVolume_field geometryRow3296_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_physicalVolume_complete"
  err.flush

noncomputable def geometryRow3296_meanGapNumeratorChars : List Char := ['1', '5', '1', '9', '2', '4', '1']
noncomputable def geometryRow3296_meanGapDenominatorChars : List Char := ['1', '3', '2', '9', '7', '5', '0', '0', '0', '0']
noncomputable def geometryRow3296_meanGapText : String := String.ofList (geometryRow3296_meanGapNumeratorChars ++ '/' :: geometryRow3296_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_meanGap_before_field"
  err.flush

theorem geometryRow3296_meanGap_field :
    geometryRowsJson3296.getObjVal? "mean_gap" = .ok (.str geometryRow3296_meanGapText) := by rfl

theorem geometryRow3296_meanGap_numerator_no_slash :
    geometryRow3296_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3296_meanGap_numerator_parse :
    SourceJson.intChars geometryRow3296_meanGapNumeratorChars = some (1519241 : Int) := by decide +kernel

theorem geometryRow3296_meanGap_denominator_parse :
    SourceJson.intChars geometryRow3296_meanGapDenominatorChars = some (1329750000 : Int) := by decide +kernel

theorem geometryRow3296_meanGap_denominator_nonzero : (1329750000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3296_meanGap_parse :
    parseRational geometryRow3296_meanGapText = .ok geometryRowsTyped3296.meanGap :=
  original_rational_fraction_of_chars geometryRow3296_meanGapNumeratorChars geometryRow3296_meanGapDenominatorChars
    (1519241 : Int) (1329750000 : Int)
    geometryRow3296_meanGap_numerator_no_slash geometryRow3296_meanGap_numerator_parse
    geometryRow3296_meanGap_denominator_parse geometryRow3296_meanGap_denominator_nonzero

theorem geometryRow3296_meanGap_read :
    rationalField geometryRowsJson3296 "mean_gap" = .ok geometryRowsTyped3296.meanGap :=
  original_rationalField_of_string geometryRowsJson3296 "mean_gap" geometryRow3296_meanGapText
    geometryRowsTyped3296.meanGap geometryRow3296_meanGap_field geometryRow3296_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_meanGap_complete"
  err.flush

noncomputable def geometryRow3296_jensenBoundNumeratorChars : List Char := ['6', '5', '0', '1', '1', '1', '9', '2', '3', '3', '8', '0', '5', '3', '7', '9', '7', '8', '8', '8', '2', '5', '9', '7', '0', '7', '7', '1', '2', '5', '3', '8', '5', '5', '5', '0', '6', '7', '1', '6', '8', '5', '9', '3', '9', '6', '4', '0', '3', '5', '2', '4', '2', '5', '7', '8', '2', '6', '7', '3', '7', '1', '4', '2', '2', '0', '2', '0', '7', '6', '1', '7', '3', '7', '4', '2', '5', '8', '7', '2', '4', '4', '9', '4', '2', '5', '4', '8', '7', '8', '8', '7', '7', '8', '8', '3', '7', '2', '6', '2', '2', '3', '5', '7', '9', '2', '0', '2', '5', '5', '7', '5', '5', '7', '3', '4', '1', '1', '9', '9', '6', '4', '3', '3', '5', '1', '4', '0', '9', '8', '7', '7', '8', '9', '1', '6', '1', '9', '7', '2', '5', '9', '4', '4', '7', '1', '1', '3', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3296_jensenBoundDenominatorChars : List Char := ['1', '2', '1', '9', '9', '6', '4', '0', '3', '3', '0', '7', '4', '6', '3', '6', '5', '7', '5', '6', '6', '8', '4', '5', '5', '6', '8', '1', '0', '5', '7', '0', '0', '6', '4', '1', '3', '0', '4', '4', '8', '6', '5', '8', '1', '7', '8', '2', '9', '4', '6', '8', '3', '2', '7', '3', '1', '1', '6', '3', '3', '4', '2', '0', '2', '8', '4', '1', '8', '9', '7', '0', '0', '9', '2', '5', '7', '5', '4', '2', '0', '0', '9', '6', '0', '2', '8', '3', '7', '0', '1', '7', '8', '9', '1', '4', '4', '1', '3', '5', '9', '5', '2', '6', '7', '5', '8', '6', '0', '8', '4', '2', '1', '5', '5', '5', '4', '6', '8', '0', '1', '0', '8', '9', '0', '0', '6', '3', '7', '6', '9', '2', '2', '3', '3', '3', '0', '8', '3', '5', '1', '4', '4', '9', '6', '7', '4', '0', '6', '4', '8', '6', '5', '8', '6', '8', '5', '9', '7', '8', '2', '9', '5', '6', '9', '7', '7', '2', '3', '1', '1', '1', '1', '7', '2', '7', '8', '5', '5', '1', '2', '7', '9', '6', '4', '4', '7']
noncomputable def geometryRow3296_jensenBoundText : String := String.ofList (geometryRow3296_jensenBoundNumeratorChars ++ '/' :: geometryRow3296_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_jensenBound_before_field"
  err.flush

theorem geometryRow3296_jensenBound_field :
    geometryRowsJson3296.getObjVal? "jensen_bound" = .ok (.str geometryRow3296_jensenBoundText) := by rfl

theorem geometryRow3296_jensenBound_numerator_no_slash :
    geometryRow3296_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3296_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow3296_jensenBoundNumeratorChars = some (65011192338053797888259707712538555067168593964035242578267371422020761737425872449425487887788372622357920255755734119964335140987789161972594471138320000000000000000000000 : Int) := by decide +kernel

theorem geometryRow3296_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow3296_jensenBoundDenominatorChars = some (1219964033074636575668455681057006413044865817829468327311633420284189700925754200960283701789144135952675860842155546801089006376922333083514496740648658685978295697723111172785512796447 : Int) := by decide +kernel

theorem geometryRow3296_jensenBound_denominator_nonzero : (1219964033074636575668455681057006413044865817829468327311633420284189700925754200960283701789144135952675860842155546801089006376922333083514496740648658685978295697723111172785512796447 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3296_jensenBound_parse :
    parseRational geometryRow3296_jensenBoundText = .ok geometryRowsTyped3296.jensenBound :=
  original_rational_fraction_of_chars geometryRow3296_jensenBoundNumeratorChars geometryRow3296_jensenBoundDenominatorChars
    (65011192338053797888259707712538555067168593964035242578267371422020761737425872449425487887788372622357920255755734119964335140987789161972594471138320000000000000000000000 : Int) (1219964033074636575668455681057006413044865817829468327311633420284189700925754200960283701789144135952675860842155546801089006376922333083514496740648658685978295697723111172785512796447 : Int)
    geometryRow3296_jensenBound_numerator_no_slash geometryRow3296_jensenBound_numerator_parse
    geometryRow3296_jensenBound_denominator_parse geometryRow3296_jensenBound_denominator_nonzero

theorem geometryRow3296_jensenBound_read :
    rationalField geometryRowsJson3296 "jensen_bound" = .ok geometryRowsTyped3296.jensenBound :=
  original_rationalField_of_string geometryRowsJson3296 "jensen_bound" geometryRow3296_jensenBoundText
    geometryRowsTyped3296.jensenBound geometryRow3296_jensenBound_field geometryRow3296_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_factorMaxima_before"
  err.flush

theorem geometryRow3296_factorMaxima_read :
    rationalArrayField geometryRowsJson3296 "factor_maxima" = .ok geometryRowsTyped3296.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_gapWeightedMeans_before"
  err.flush

theorem geometryRow3296_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson3296 "gap_weighted_means" = .ok geometryRowsTyped3296.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow3296_floorChars : List Char := ['4', '2', '2', '2', '0', '2', '3', '9', '0', '5', '7', '5', '7', '4', '7', '8']
noncomputable def geometryRow3296_floorText : String := String.ofList geometryRow3296_floorChars

theorem geometryRow3296_floor_text_read :
    geometryRowsJson3296.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow3296_floorText := by rfl

theorem geometryRow3296_floor_chars_parse :
    SourceJson.intChars geometryRow3296_floorChars = some (4222023905757478 : Int) := by decide +kernel

theorem geometryRow3296_floor_parse :
    parseInteger geometryRow3296_floorText = .ok geometryRowsTyped3296.jensenFloorQ96 := by
  simp only [geometryRow3296_floorText, parseInteger, String.toList_ofList, geometryRow3296_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_3296 :
    decodeGeometryRow geometryRowsJson3296 = .ok geometryRowsTyped3296 :=
  original_geometryRow_of_fields geometryRowsJson3296 geometryRowsTyped3296 geometryRow3296_floorText
    geometryRow3296_simplexId_read geometryRow3296_vertexIds_read
    geometryRow3296_physicalVolume_read geometryRow3296_meanGap_read
    geometryRow3296_factorMaxima_read geometryRow3296_gapWeightedMeans_read
    geometryRow3296_jensenBound_read geometryRow3296_floor_text_read geometryRow3296_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3296_original_decoder_complete"
  err.flush

theorem geometryRow3296_shape :
    geometryRowsTyped3296.simplexId = 3296 ∧
    geometryRowsTyped3296.vertexIds.size = 9 ∧ geometryRowsTyped3296.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped3296.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped3296.factorMaxima.size = 10 ∧ geometryRowsTyped3296.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson3297 : SourceJson :=
  (SimplicesBlock412.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped3297 : GeometryRow :=
  { simplexId := 3297,
    vertexIds := #[139, 133, 114, 113, 99, 62, 60, 49, 40],
    physicalVolume := ((520736686468908098465511529827995563271 : ℚ) / (32896812009600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((7811 : ℚ) / (13500000 : ℚ)),
    factorMaxima := #[((10254 : ℚ) / (171875 : ℚ)), ((10254 : ℚ) / (171875 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((3500143 : ℚ) / (47500000 : ℚ)), ((207029 : ℚ) / (2968750 : ℚ)), ((207029 : ℚ) / (2968750 : ℚ)), ((11 : ℚ) / (336 : ℚ)), ((11 : ℚ) / (336 : ℚ))],
    gapWeightedMeans := #[((337694321969 : ℚ) / (8393962500000 : ℚ)), ((173218177057 : ℚ) / (4196981250000 : ℚ)), ((589188601913 : ℚ) / (4974200000000 : ℚ)), ((4370314835767 : ℚ) / (44767800000000 : ℚ)), ((4017094357387 : ℚ) / (44767800000000 : ℚ)), ((31220575023 : ℚ) / (452200000000 : ℚ)), ((2977798248223 : ℚ) / (44767800000000 : ℚ)), ((1426094030029 : ℚ) / (22383900000000 : ℚ)), ((171447072383 : ℚ) / (6715170000000 : ℚ)), ((102572045993 : ℚ) / (4476780000000 : ℚ))],
    jensenBound := ((123517491003756808258190273637865734819482733678083468858468822690988751745634266250000000000000000000 : ℚ) / (994162419859471621481339356452324301655515578151906488649968608294623801027958841091981595590976971783137754885781 : ℚ)),
    jensenFloorQ96 := (9843526223796633 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_simplexId_before"
  err.flush

theorem geometryRow3297_simplexId_read :
    geometryRowsJson3297.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped3297.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_vertexIds_before"
  err.flush

theorem geometryRow3297_vertexIds_read :
    geometryRowsJson3297.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped3297.vertexIds := by decide +kernel

noncomputable def geometryRow3297_physicalVolumeNumeratorChars : List Char := ['5', '2', '0', '7', '3', '6', '6', '8', '6', '4', '6', '8', '9', '0', '8', '0', '9', '8', '4', '6', '5', '5', '1', '1', '5', '2', '9', '8', '2', '7', '9', '9', '5', '5', '6', '3', '2', '7', '1']
noncomputable def geometryRow3297_physicalVolumeDenominatorChars : List Char := ['3', '2', '8', '9', '6', '8', '1', '2', '0', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3297_physicalVolumeText : String := String.ofList (geometryRow3297_physicalVolumeNumeratorChars ++ '/' :: geometryRow3297_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_physicalVolume_before_field"
  err.flush

theorem geometryRow3297_physicalVolume_field :
    geometryRowsJson3297.getObjVal? "physical_volume" = .ok (.str geometryRow3297_physicalVolumeText) := by rfl

theorem geometryRow3297_physicalVolume_numerator_no_slash :
    geometryRow3297_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3297_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow3297_physicalVolumeNumeratorChars = some (520736686468908098465511529827995563271 : Int) := by decide +kernel

theorem geometryRow3297_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow3297_physicalVolumeDenominatorChars = some (32896812009600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow3297_physicalVolume_denominator_nonzero : (32896812009600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3297_physicalVolume_parse :
    parseRational geometryRow3297_physicalVolumeText = .ok geometryRowsTyped3297.physicalVolume :=
  original_rational_fraction_of_chars geometryRow3297_physicalVolumeNumeratorChars geometryRow3297_physicalVolumeDenominatorChars
    (520736686468908098465511529827995563271 : Int) (32896812009600000000000000000000000000000000000000000000000000 : Int)
    geometryRow3297_physicalVolume_numerator_no_slash geometryRow3297_physicalVolume_numerator_parse
    geometryRow3297_physicalVolume_denominator_parse geometryRow3297_physicalVolume_denominator_nonzero

theorem geometryRow3297_physicalVolume_read :
    rationalField geometryRowsJson3297 "physical_volume" = .ok geometryRowsTyped3297.physicalVolume :=
  original_rationalField_of_string geometryRowsJson3297 "physical_volume" geometryRow3297_physicalVolumeText
    geometryRowsTyped3297.physicalVolume geometryRow3297_physicalVolume_field geometryRow3297_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_physicalVolume_complete"
  err.flush

noncomputable def geometryRow3297_meanGapNumeratorChars : List Char := ['7', '8', '1', '1']
noncomputable def geometryRow3297_meanGapDenominatorChars : List Char := ['1', '3', '5', '0', '0', '0', '0', '0']
noncomputable def geometryRow3297_meanGapText : String := String.ofList (geometryRow3297_meanGapNumeratorChars ++ '/' :: geometryRow3297_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_meanGap_before_field"
  err.flush

theorem geometryRow3297_meanGap_field :
    geometryRowsJson3297.getObjVal? "mean_gap" = .ok (.str geometryRow3297_meanGapText) := by rfl

theorem geometryRow3297_meanGap_numerator_no_slash :
    geometryRow3297_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3297_meanGap_numerator_parse :
    SourceJson.intChars geometryRow3297_meanGapNumeratorChars = some (7811 : Int) := by decide +kernel

theorem geometryRow3297_meanGap_denominator_parse :
    SourceJson.intChars geometryRow3297_meanGapDenominatorChars = some (13500000 : Int) := by decide +kernel

theorem geometryRow3297_meanGap_denominator_nonzero : (13500000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3297_meanGap_parse :
    parseRational geometryRow3297_meanGapText = .ok geometryRowsTyped3297.meanGap :=
  original_rational_fraction_of_chars geometryRow3297_meanGapNumeratorChars geometryRow3297_meanGapDenominatorChars
    (7811 : Int) (13500000 : Int)
    geometryRow3297_meanGap_numerator_no_slash geometryRow3297_meanGap_numerator_parse
    geometryRow3297_meanGap_denominator_parse geometryRow3297_meanGap_denominator_nonzero

theorem geometryRow3297_meanGap_read :
    rationalField geometryRowsJson3297 "mean_gap" = .ok geometryRowsTyped3297.meanGap :=
  original_rationalField_of_string geometryRowsJson3297 "mean_gap" geometryRow3297_meanGapText
    geometryRowsTyped3297.meanGap geometryRow3297_meanGap_field geometryRow3297_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_meanGap_complete"
  err.flush

noncomputable def geometryRow3297_jensenBoundNumeratorChars : List Char := ['1', '2', '3', '5', '1', '7', '4', '9', '1', '0', '0', '3', '7', '5', '6', '8', '0', '8', '2', '5', '8', '1', '9', '0', '2', '7', '3', '6', '3', '7', '8', '6', '5', '7', '3', '4', '8', '1', '9', '4', '8', '2', '7', '3', '3', '6', '7', '8', '0', '8', '3', '4', '6', '8', '8', '5', '8', '4', '6', '8', '8', '2', '2', '6', '9', '0', '9', '8', '8', '7', '5', '1', '7', '4', '5', '6', '3', '4', '2', '6', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3297_jensenBoundDenominatorChars : List Char := ['9', '9', '4', '1', '6', '2', '4', '1', '9', '8', '5', '9', '4', '7', '1', '6', '2', '1', '4', '8', '1', '3', '3', '9', '3', '5', '6', '4', '5', '2', '3', '2', '4', '3', '0', '1', '6', '5', '5', '5', '1', '5', '5', '7', '8', '1', '5', '1', '9', '0', '6', '4', '8', '8', '6', '4', '9', '9', '6', '8', '6', '0', '8', '2', '9', '4', '6', '2', '3', '8', '0', '1', '0', '2', '7', '9', '5', '8', '8', '4', '1', '0', '9', '1', '9', '8', '1', '5', '9', '5', '5', '9', '0', '9', '7', '6', '9', '7', '1', '7', '8', '3', '1', '3', '7', '7', '5', '4', '8', '8', '5', '7', '8', '1']
noncomputable def geometryRow3297_jensenBoundText : String := String.ofList (geometryRow3297_jensenBoundNumeratorChars ++ '/' :: geometryRow3297_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_jensenBound_before_field"
  err.flush

theorem geometryRow3297_jensenBound_field :
    geometryRowsJson3297.getObjVal? "jensen_bound" = .ok (.str geometryRow3297_jensenBoundText) := by rfl

theorem geometryRow3297_jensenBound_numerator_no_slash :
    geometryRow3297_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3297_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow3297_jensenBoundNumeratorChars = some (123517491003756808258190273637865734819482733678083468858468822690988751745634266250000000000000000000 : Int) := by decide +kernel

theorem geometryRow3297_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow3297_jensenBoundDenominatorChars = some (994162419859471621481339356452324301655515578151906488649968608294623801027958841091981595590976971783137754885781 : Int) := by decide +kernel

theorem geometryRow3297_jensenBound_denominator_nonzero : (994162419859471621481339356452324301655515578151906488649968608294623801027958841091981595590976971783137754885781 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3297_jensenBound_parse :
    parseRational geometryRow3297_jensenBoundText = .ok geometryRowsTyped3297.jensenBound :=
  original_rational_fraction_of_chars geometryRow3297_jensenBoundNumeratorChars geometryRow3297_jensenBoundDenominatorChars
    (123517491003756808258190273637865734819482733678083468858468822690988751745634266250000000000000000000 : Int) (994162419859471621481339356452324301655515578151906488649968608294623801027958841091981595590976971783137754885781 : Int)
    geometryRow3297_jensenBound_numerator_no_slash geometryRow3297_jensenBound_numerator_parse
    geometryRow3297_jensenBound_denominator_parse geometryRow3297_jensenBound_denominator_nonzero

theorem geometryRow3297_jensenBound_read :
    rationalField geometryRowsJson3297 "jensen_bound" = .ok geometryRowsTyped3297.jensenBound :=
  original_rationalField_of_string geometryRowsJson3297 "jensen_bound" geometryRow3297_jensenBoundText
    geometryRowsTyped3297.jensenBound geometryRow3297_jensenBound_field geometryRow3297_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_factorMaxima_before"
  err.flush

theorem geometryRow3297_factorMaxima_read :
    rationalArrayField geometryRowsJson3297 "factor_maxima" = .ok geometryRowsTyped3297.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_gapWeightedMeans_before"
  err.flush

theorem geometryRow3297_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson3297 "gap_weighted_means" = .ok geometryRowsTyped3297.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow3297_floorChars : List Char := ['9', '8', '4', '3', '5', '2', '6', '2', '2', '3', '7', '9', '6', '6', '3', '3']
noncomputable def geometryRow3297_floorText : String := String.ofList geometryRow3297_floorChars

theorem geometryRow3297_floor_text_read :
    geometryRowsJson3297.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow3297_floorText := by rfl

theorem geometryRow3297_floor_chars_parse :
    SourceJson.intChars geometryRow3297_floorChars = some (9843526223796633 : Int) := by decide +kernel

theorem geometryRow3297_floor_parse :
    parseInteger geometryRow3297_floorText = .ok geometryRowsTyped3297.jensenFloorQ96 := by
  simp only [geometryRow3297_floorText, parseInteger, String.toList_ofList, geometryRow3297_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_3297 :
    decodeGeometryRow geometryRowsJson3297 = .ok geometryRowsTyped3297 :=
  original_geometryRow_of_fields geometryRowsJson3297 geometryRowsTyped3297 geometryRow3297_floorText
    geometryRow3297_simplexId_read geometryRow3297_vertexIds_read
    geometryRow3297_physicalVolume_read geometryRow3297_meanGap_read
    geometryRow3297_factorMaxima_read geometryRow3297_gapWeightedMeans_read
    geometryRow3297_jensenBound_read geometryRow3297_floor_text_read geometryRow3297_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3297_original_decoder_complete"
  err.flush

theorem geometryRow3297_shape :
    geometryRowsTyped3297.simplexId = 3297 ∧
    geometryRowsTyped3297.vertexIds.size = 9 ∧ geometryRowsTyped3297.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped3297.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped3297.factorMaxima.size = 10 ∧ geometryRowsTyped3297.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson3298 : SourceJson :=
  (SimplicesBlock412.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped3298 : GeometryRow :=
  { simplexId := 3298,
    vertexIds := #[139, 133, 114, 113, 99, 62, 60, 52, 40],
    physicalVolume := ((6095407793368164210092097546784016777611 : ℚ) / (762607914768000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((7811 : ℚ) / (13500000 : ℚ)),
    factorMaxima := #[((93743 : ℚ) / (1750000 : ℚ)), ((93743 : ℚ) / (1750000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((3500143 : ℚ) / (47500000 : ℚ)), ((1187489 : ℚ) / (17000000 : ℚ)), ((1187489 : ℚ) / (17000000 : ℚ)), ((11 : ℚ) / (336 : ℚ)), ((11 : ℚ) / (336 : ℚ))],
    gapWeightedMeans := #[((119736305791 : ℚ) / (3052350000000 : ℚ)), ((122915226571 : ℚ) / (3052350000000 : ℚ)), ((53572110883 : ℚ) / (452200000000 : ℚ)), ((397249990877 : ℚ) / (4069800000000 : ℚ)), ((365139038297 : ℚ) / (4069800000000 : ℚ)), ((31199651463 : ℚ) / (452200000000 : ℚ)), ((272690100503 : ℚ) / (4069800000000 : ℚ)), ((32658874061 : ℚ) / (508725000000 : ℚ)), ((15606640621 : ℚ) / (610470000000 : ℚ)), ((14941483 : ℚ) / (651168000 : ℚ))],
    jensenBound := ((30050851367244951035449106638700326207360025340610124535100533707294371200000000000000000 : ℚ) / (463499153765558486462173057865158459617185909951819719067923765061325372653373275186115072397898471707 : ℚ)),
    jensenFloorQ96 := (5136738042504281 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_simplexId_before"
  err.flush

theorem geometryRow3298_simplexId_read :
    geometryRowsJson3298.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped3298.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_vertexIds_before"
  err.flush

theorem geometryRow3298_vertexIds_read :
    geometryRowsJson3298.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped3298.vertexIds := by decide +kernel

noncomputable def geometryRow3298_physicalVolumeNumeratorChars : List Char := ['6', '0', '9', '5', '4', '0', '7', '7', '9', '3', '3', '6', '8', '1', '6', '4', '2', '1', '0', '0', '9', '2', '0', '9', '7', '5', '4', '6', '7', '8', '4', '0', '1', '6', '7', '7', '7', '6', '1', '1']
noncomputable def geometryRow3298_physicalVolumeDenominatorChars : List Char := ['7', '6', '2', '6', '0', '7', '9', '1', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3298_physicalVolumeText : String := String.ofList (geometryRow3298_physicalVolumeNumeratorChars ++ '/' :: geometryRow3298_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_physicalVolume_before_field"
  err.flush

theorem geometryRow3298_physicalVolume_field :
    geometryRowsJson3298.getObjVal? "physical_volume" = .ok (.str geometryRow3298_physicalVolumeText) := by rfl

theorem geometryRow3298_physicalVolume_numerator_no_slash :
    geometryRow3298_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3298_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow3298_physicalVolumeNumeratorChars = some (6095407793368164210092097546784016777611 : Int) := by decide +kernel

theorem geometryRow3298_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow3298_physicalVolumeDenominatorChars = some (762607914768000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow3298_physicalVolume_denominator_nonzero : (762607914768000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3298_physicalVolume_parse :
    parseRational geometryRow3298_physicalVolumeText = .ok geometryRowsTyped3298.physicalVolume :=
  original_rational_fraction_of_chars geometryRow3298_physicalVolumeNumeratorChars geometryRow3298_physicalVolumeDenominatorChars
    (6095407793368164210092097546784016777611 : Int) (762607914768000000000000000000000000000000000000000000000000000 : Int)
    geometryRow3298_physicalVolume_numerator_no_slash geometryRow3298_physicalVolume_numerator_parse
    geometryRow3298_physicalVolume_denominator_parse geometryRow3298_physicalVolume_denominator_nonzero

theorem geometryRow3298_physicalVolume_read :
    rationalField geometryRowsJson3298 "physical_volume" = .ok geometryRowsTyped3298.physicalVolume :=
  original_rationalField_of_string geometryRowsJson3298 "physical_volume" geometryRow3298_physicalVolumeText
    geometryRowsTyped3298.physicalVolume geometryRow3298_physicalVolume_field geometryRow3298_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_physicalVolume_complete"
  err.flush

noncomputable def geometryRow3298_meanGapNumeratorChars : List Char := ['7', '8', '1', '1']
noncomputable def geometryRow3298_meanGapDenominatorChars : List Char := ['1', '3', '5', '0', '0', '0', '0', '0']
noncomputable def geometryRow3298_meanGapText : String := String.ofList (geometryRow3298_meanGapNumeratorChars ++ '/' :: geometryRow3298_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_meanGap_before_field"
  err.flush

theorem geometryRow3298_meanGap_field :
    geometryRowsJson3298.getObjVal? "mean_gap" = .ok (.str geometryRow3298_meanGapText) := by rfl

theorem geometryRow3298_meanGap_numerator_no_slash :
    geometryRow3298_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3298_meanGap_numerator_parse :
    SourceJson.intChars geometryRow3298_meanGapNumeratorChars = some (7811 : Int) := by decide +kernel

theorem geometryRow3298_meanGap_denominator_parse :
    SourceJson.intChars geometryRow3298_meanGapDenominatorChars = some (13500000 : Int) := by decide +kernel

theorem geometryRow3298_meanGap_denominator_nonzero : (13500000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3298_meanGap_parse :
    parseRational geometryRow3298_meanGapText = .ok geometryRowsTyped3298.meanGap :=
  original_rational_fraction_of_chars geometryRow3298_meanGapNumeratorChars geometryRow3298_meanGapDenominatorChars
    (7811 : Int) (13500000 : Int)
    geometryRow3298_meanGap_numerator_no_slash geometryRow3298_meanGap_numerator_parse
    geometryRow3298_meanGap_denominator_parse geometryRow3298_meanGap_denominator_nonzero

theorem geometryRow3298_meanGap_read :
    rationalField geometryRowsJson3298 "mean_gap" = .ok geometryRowsTyped3298.meanGap :=
  original_rationalField_of_string geometryRowsJson3298 "mean_gap" geometryRow3298_meanGapText
    geometryRowsTyped3298.meanGap geometryRow3298_meanGap_field geometryRow3298_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_meanGap_complete"
  err.flush

noncomputable def geometryRow3298_jensenBoundNumeratorChars : List Char := ['3', '0', '0', '5', '0', '8', '5', '1', '3', '6', '7', '2', '4', '4', '9', '5', '1', '0', '3', '5', '4', '4', '9', '1', '0', '6', '6', '3', '8', '7', '0', '0', '3', '2', '6', '2', '0', '7', '3', '6', '0', '0', '2', '5', '3', '4', '0', '6', '1', '0', '1', '2', '4', '5', '3', '5', '1', '0', '0', '5', '3', '3', '7', '0', '7', '2', '9', '4', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3298_jensenBoundDenominatorChars : List Char := ['4', '6', '3', '4', '9', '9', '1', '5', '3', '7', '6', '5', '5', '5', '8', '4', '8', '6', '4', '6', '2', '1', '7', '3', '0', '5', '7', '8', '6', '5', '1', '5', '8', '4', '5', '9', '6', '1', '7', '1', '8', '5', '9', '0', '9', '9', '5', '1', '8', '1', '9', '7', '1', '9', '0', '6', '7', '9', '2', '3', '7', '6', '5', '0', '6', '1', '3', '2', '5', '3', '7', '2', '6', '5', '3', '3', '7', '3', '2', '7', '5', '1', '8', '6', '1', '1', '5', '0', '7', '2', '3', '9', '7', '8', '9', '8', '4', '7', '1', '7', '0', '7']
noncomputable def geometryRow3298_jensenBoundText : String := String.ofList (geometryRow3298_jensenBoundNumeratorChars ++ '/' :: geometryRow3298_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_jensenBound_before_field"
  err.flush

theorem geometryRow3298_jensenBound_field :
    geometryRowsJson3298.getObjVal? "jensen_bound" = .ok (.str geometryRow3298_jensenBoundText) := by rfl

theorem geometryRow3298_jensenBound_numerator_no_slash :
    geometryRow3298_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3298_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow3298_jensenBoundNumeratorChars = some (30050851367244951035449106638700326207360025340610124535100533707294371200000000000000000 : Int) := by decide +kernel

theorem geometryRow3298_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow3298_jensenBoundDenominatorChars = some (463499153765558486462173057865158459617185909951819719067923765061325372653373275186115072397898471707 : Int) := by decide +kernel

theorem geometryRow3298_jensenBound_denominator_nonzero : (463499153765558486462173057865158459617185909951819719067923765061325372653373275186115072397898471707 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3298_jensenBound_parse :
    parseRational geometryRow3298_jensenBoundText = .ok geometryRowsTyped3298.jensenBound :=
  original_rational_fraction_of_chars geometryRow3298_jensenBoundNumeratorChars geometryRow3298_jensenBoundDenominatorChars
    (30050851367244951035449106638700326207360025340610124535100533707294371200000000000000000 : Int) (463499153765558486462173057865158459617185909951819719067923765061325372653373275186115072397898471707 : Int)
    geometryRow3298_jensenBound_numerator_no_slash geometryRow3298_jensenBound_numerator_parse
    geometryRow3298_jensenBound_denominator_parse geometryRow3298_jensenBound_denominator_nonzero

theorem geometryRow3298_jensenBound_read :
    rationalField geometryRowsJson3298 "jensen_bound" = .ok geometryRowsTyped3298.jensenBound :=
  original_rationalField_of_string geometryRowsJson3298 "jensen_bound" geometryRow3298_jensenBoundText
    geometryRowsTyped3298.jensenBound geometryRow3298_jensenBound_field geometryRow3298_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_factorMaxima_before"
  err.flush

theorem geometryRow3298_factorMaxima_read :
    rationalArrayField geometryRowsJson3298 "factor_maxima" = .ok geometryRowsTyped3298.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_gapWeightedMeans_before"
  err.flush

theorem geometryRow3298_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson3298 "gap_weighted_means" = .ok geometryRowsTyped3298.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow3298_floorChars : List Char := ['5', '1', '3', '6', '7', '3', '8', '0', '4', '2', '5', '0', '4', '2', '8', '1']
noncomputable def geometryRow3298_floorText : String := String.ofList geometryRow3298_floorChars

theorem geometryRow3298_floor_text_read :
    geometryRowsJson3298.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow3298_floorText := by rfl

theorem geometryRow3298_floor_chars_parse :
    SourceJson.intChars geometryRow3298_floorChars = some (5136738042504281 : Int) := by decide +kernel

theorem geometryRow3298_floor_parse :
    parseInteger geometryRow3298_floorText = .ok geometryRowsTyped3298.jensenFloorQ96 := by
  simp only [geometryRow3298_floorText, parseInteger, String.toList_ofList, geometryRow3298_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_3298 :
    decodeGeometryRow geometryRowsJson3298 = .ok geometryRowsTyped3298 :=
  original_geometryRow_of_fields geometryRowsJson3298 geometryRowsTyped3298 geometryRow3298_floorText
    geometryRow3298_simplexId_read geometryRow3298_vertexIds_read
    geometryRow3298_physicalVolume_read geometryRow3298_meanGap_read
    geometryRow3298_factorMaxima_read geometryRow3298_gapWeightedMeans_read
    geometryRow3298_jensenBound_read geometryRow3298_floor_text_read geometryRow3298_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3298_original_decoder_complete"
  err.flush

theorem geometryRow3298_shape :
    geometryRowsTyped3298.simplexId = 3298 ∧
    geometryRowsTyped3298.vertexIds.size = 9 ∧ geometryRowsTyped3298.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped3298.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped3298.factorMaxima.size = 10 ∧ geometryRowsTyped3298.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson3299 : SourceJson :=
  (SimplicesBlock412.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped3299 : GeometryRow :=
  { simplexId := 3299,
    vertexIds := #[139, 133, 114, 113, 99, 80, 49, 8, 3],
    physicalVolume := ((137180781980888466382229728861410533877463 : ℚ) / (2849408077824000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((23495069 : ℚ) / (25560000000 : ℚ)),
    factorMaxima := #[((4265657 : ℚ) / (71000000 : ℚ)), ((1148427 : ℚ) / (17750000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((3370407 : ℚ) / (40000000 : ℚ)), ((828137 : ℚ) / (12000000 : ℚ)), ((340991 : ℚ) / (5000000 : ℚ)), ((1484407 : ℚ) / (54000000 : ℚ)), ((484403 : ℚ) / (18000000 : ℚ))],
    gapWeightedMeans := #[((110234089979783943629 : ℚ) / (2461958276322600000000 : ℚ)), ((368235289288671231677 : ℚ) / (8001364398048450000000 : ℚ)), ((32868758676598963523 : ℚ) / (280749628001700000000 : ℚ)), ((530968931260743358199 : ℚ) / (5334242932032300000000 : ℚ)), ((25730602753067963651 : ℚ) / (280749628001700000000 : ℚ)), ((1895089963287881669 : ℚ) / (25522693454700000000 : ℚ)), ((12025270791456972433 : ℚ) / (187166418667800000000 : ℚ)), ((4312543630724169413 : ℚ) / (70187407000425000000 : ℚ)), ((18122914628262526567 : ℚ) / (800136439804845000000 : ℚ)), ((7123165414644371101 : ℚ) / (355616195468820000000 : ℚ))],
    jensenBound := ((979101353368006222130320461885267888748033697388648252234678029086932377336236780595798023255325094265218728556352143472987275738674992407136465232787197706086926716906738281250000000 : ℚ) / (1618829136626436669637983032280660126893480950087531208347239621812830819631568299656702482968071240024799225564724752030837967368825724338814244196253946458918631800439366187733058343008124115779 : ℚ)),
    jensenFloorQ96 := (47918831819541971 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_simplexId_before"
  err.flush

theorem geometryRow3299_simplexId_read :
    geometryRowsJson3299.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped3299.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_vertexIds_before"
  err.flush

theorem geometryRow3299_vertexIds_read :
    geometryRowsJson3299.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped3299.vertexIds := by decide +kernel

noncomputable def geometryRow3299_physicalVolumeNumeratorChars : List Char := ['1', '3', '7', '1', '8', '0', '7', '8', '1', '9', '8', '0', '8', '8', '8', '4', '6', '6', '3', '8', '2', '2', '2', '9', '7', '2', '8', '8', '6', '1', '4', '1', '0', '5', '3', '3', '8', '7', '7', '4', '6', '3']
noncomputable def geometryRow3299_physicalVolumeDenominatorChars : List Char := ['2', '8', '4', '9', '4', '0', '8', '0', '7', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3299_physicalVolumeText : String := String.ofList (geometryRow3299_physicalVolumeNumeratorChars ++ '/' :: geometryRow3299_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_physicalVolume_before_field"
  err.flush

theorem geometryRow3299_physicalVolume_field :
    geometryRowsJson3299.getObjVal? "physical_volume" = .ok (.str geometryRow3299_physicalVolumeText) := by rfl

theorem geometryRow3299_physicalVolume_numerator_no_slash :
    geometryRow3299_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3299_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow3299_physicalVolumeNumeratorChars = some (137180781980888466382229728861410533877463 : Int) := by decide +kernel

theorem geometryRow3299_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow3299_physicalVolumeDenominatorChars = some (2849408077824000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow3299_physicalVolume_denominator_nonzero : (2849408077824000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3299_physicalVolume_parse :
    parseRational geometryRow3299_physicalVolumeText = .ok geometryRowsTyped3299.physicalVolume :=
  original_rational_fraction_of_chars geometryRow3299_physicalVolumeNumeratorChars geometryRow3299_physicalVolumeDenominatorChars
    (137180781980888466382229728861410533877463 : Int) (2849408077824000000000000000000000000000000000000000000000000000 : Int)
    geometryRow3299_physicalVolume_numerator_no_slash geometryRow3299_physicalVolume_numerator_parse
    geometryRow3299_physicalVolume_denominator_parse geometryRow3299_physicalVolume_denominator_nonzero

theorem geometryRow3299_physicalVolume_read :
    rationalField geometryRowsJson3299 "physical_volume" = .ok geometryRowsTyped3299.physicalVolume :=
  original_rationalField_of_string geometryRowsJson3299 "physical_volume" geometryRow3299_physicalVolumeText
    geometryRowsTyped3299.physicalVolume geometryRow3299_physicalVolume_field geometryRow3299_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_physicalVolume_complete"
  err.flush

noncomputable def geometryRow3299_meanGapNumeratorChars : List Char := ['2', '3', '4', '9', '5', '0', '6', '9']
noncomputable def geometryRow3299_meanGapDenominatorChars : List Char := ['2', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3299_meanGapText : String := String.ofList (geometryRow3299_meanGapNumeratorChars ++ '/' :: geometryRow3299_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_meanGap_before_field"
  err.flush

theorem geometryRow3299_meanGap_field :
    geometryRowsJson3299.getObjVal? "mean_gap" = .ok (.str geometryRow3299_meanGapText) := by rfl

theorem geometryRow3299_meanGap_numerator_no_slash :
    geometryRow3299_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3299_meanGap_numerator_parse :
    SourceJson.intChars geometryRow3299_meanGapNumeratorChars = some (23495069 : Int) := by decide +kernel

theorem geometryRow3299_meanGap_denominator_parse :
    SourceJson.intChars geometryRow3299_meanGapDenominatorChars = some (25560000000 : Int) := by decide +kernel

theorem geometryRow3299_meanGap_denominator_nonzero : (25560000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3299_meanGap_parse :
    parseRational geometryRow3299_meanGapText = .ok geometryRowsTyped3299.meanGap :=
  original_rational_fraction_of_chars geometryRow3299_meanGapNumeratorChars geometryRow3299_meanGapDenominatorChars
    (23495069 : Int) (25560000000 : Int)
    geometryRow3299_meanGap_numerator_no_slash geometryRow3299_meanGap_numerator_parse
    geometryRow3299_meanGap_denominator_parse geometryRow3299_meanGap_denominator_nonzero

theorem geometryRow3299_meanGap_read :
    rationalField geometryRowsJson3299 "mean_gap" = .ok geometryRowsTyped3299.meanGap :=
  original_rationalField_of_string geometryRowsJson3299 "mean_gap" geometryRow3299_meanGapText
    geometryRowsTyped3299.meanGap geometryRow3299_meanGap_field geometryRow3299_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_meanGap_complete"
  err.flush

noncomputable def geometryRow3299_jensenBoundNumeratorChars : List Char := ['9', '7', '9', '1', '0', '1', '3', '5', '3', '3', '6', '8', '0', '0', '6', '2', '2', '2', '1', '3', '0', '3', '2', '0', '4', '6', '1', '8', '8', '5', '2', '6', '7', '8', '8', '8', '7', '4', '8', '0', '3', '3', '6', '9', '7', '3', '8', '8', '6', '4', '8', '2', '5', '2', '2', '3', '4', '6', '7', '8', '0', '2', '9', '0', '8', '6', '9', '3', '2', '3', '7', '7', '3', '3', '6', '2', '3', '6', '7', '8', '0', '5', '9', '5', '7', '9', '8', '0', '2', '3', '2', '5', '5', '3', '2', '5', '0', '9', '4', '2', '6', '5', '2', '1', '8', '7', '2', '8', '5', '5', '6', '3', '5', '2', '1', '4', '3', '4', '7', '2', '9', '8', '7', '2', '7', '5', '7', '3', '8', '6', '7', '4', '9', '9', '2', '4', '0', '7', '1', '3', '6', '4', '6', '5', '2', '3', '2', '7', '8', '7', '1', '9', '7', '7', '0', '6', '0', '8', '6', '9', '2', '6', '7', '1', '6', '9', '0', '6', '7', '3', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3299_jensenBoundDenominatorChars : List Char := ['1', '6', '1', '8', '8', '2', '9', '1', '3', '6', '6', '2', '6', '4', '3', '6', '6', '6', '9', '6', '3', '7', '9', '8', '3', '0', '3', '2', '2', '8', '0', '6', '6', '0', '1', '2', '6', '8', '9', '3', '4', '8', '0', '9', '5', '0', '0', '8', '7', '5', '3', '1', '2', '0', '8', '3', '4', '7', '2', '3', '9', '6', '2', '1', '8', '1', '2', '8', '3', '0', '8', '1', '9', '6', '3', '1', '5', '6', '8', '2', '9', '9', '6', '5', '6', '7', '0', '2', '4', '8', '2', '9', '6', '8', '0', '7', '1', '2', '4', '0', '0', '2', '4', '7', '9', '9', '2', '2', '5', '5', '6', '4', '7', '2', '4', '7', '5', '2', '0', '3', '0', '8', '3', '7', '9', '6', '7', '3', '6', '8', '8', '2', '5', '7', '2', '4', '3', '3', '8', '8', '1', '4', '2', '4', '4', '1', '9', '6', '2', '5', '3', '9', '4', '6', '4', '5', '8', '9', '1', '8', '6', '3', '1', '8', '0', '0', '4', '3', '9', '3', '6', '6', '1', '8', '7', '7', '3', '3', '0', '5', '8', '3', '4', '3', '0', '0', '8', '1', '2', '4', '1', '1', '5', '7', '7', '9']
noncomputable def geometryRow3299_jensenBoundText : String := String.ofList (geometryRow3299_jensenBoundNumeratorChars ++ '/' :: geometryRow3299_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_jensenBound_before_field"
  err.flush

theorem geometryRow3299_jensenBound_field :
    geometryRowsJson3299.getObjVal? "jensen_bound" = .ok (.str geometryRow3299_jensenBoundText) := by rfl

theorem geometryRow3299_jensenBound_numerator_no_slash :
    geometryRow3299_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3299_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow3299_jensenBoundNumeratorChars = some (979101353368006222130320461885267888748033697388648252234678029086932377336236780595798023255325094265218728556352143472987275738674992407136465232787197706086926716906738281250000000 : Int) := by decide +kernel

theorem geometryRow3299_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow3299_jensenBoundDenominatorChars = some (1618829136626436669637983032280660126893480950087531208347239621812830819631568299656702482968071240024799225564724752030837967368825724338814244196253946458918631800439366187733058343008124115779 : Int) := by decide +kernel

theorem geometryRow3299_jensenBound_denominator_nonzero : (1618829136626436669637983032280660126893480950087531208347239621812830819631568299656702482968071240024799225564724752030837967368825724338814244196253946458918631800439366187733058343008124115779 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3299_jensenBound_parse :
    parseRational geometryRow3299_jensenBoundText = .ok geometryRowsTyped3299.jensenBound :=
  original_rational_fraction_of_chars geometryRow3299_jensenBoundNumeratorChars geometryRow3299_jensenBoundDenominatorChars
    (979101353368006222130320461885267888748033697388648252234678029086932377336236780595798023255325094265218728556352143472987275738674992407136465232787197706086926716906738281250000000 : Int) (1618829136626436669637983032280660126893480950087531208347239621812830819631568299656702482968071240024799225564724752030837967368825724338814244196253946458918631800439366187733058343008124115779 : Int)
    geometryRow3299_jensenBound_numerator_no_slash geometryRow3299_jensenBound_numerator_parse
    geometryRow3299_jensenBound_denominator_parse geometryRow3299_jensenBound_denominator_nonzero

theorem geometryRow3299_jensenBound_read :
    rationalField geometryRowsJson3299 "jensen_bound" = .ok geometryRowsTyped3299.jensenBound :=
  original_rationalField_of_string geometryRowsJson3299 "jensen_bound" geometryRow3299_jensenBoundText
    geometryRowsTyped3299.jensenBound geometryRow3299_jensenBound_field geometryRow3299_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_factorMaxima_before"
  err.flush

theorem geometryRow3299_factorMaxima_read :
    rationalArrayField geometryRowsJson3299 "factor_maxima" = .ok geometryRowsTyped3299.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_gapWeightedMeans_before"
  err.flush

theorem geometryRow3299_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson3299 "gap_weighted_means" = .ok geometryRowsTyped3299.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow3299_floorChars : List Char := ['4', '7', '9', '1', '8', '8', '3', '1', '8', '1', '9', '5', '4', '1', '9', '7', '1']
noncomputable def geometryRow3299_floorText : String := String.ofList geometryRow3299_floorChars

theorem geometryRow3299_floor_text_read :
    geometryRowsJson3299.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow3299_floorText := by rfl

theorem geometryRow3299_floor_chars_parse :
    SourceJson.intChars geometryRow3299_floorChars = some (47918831819541971 : Int) := by decide +kernel

theorem geometryRow3299_floor_parse :
    parseInteger geometryRow3299_floorText = .ok geometryRowsTyped3299.jensenFloorQ96 := by
  simp only [geometryRow3299_floorText, parseInteger, String.toList_ofList, geometryRow3299_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_3299 :
    decodeGeometryRow geometryRowsJson3299 = .ok geometryRowsTyped3299 :=
  original_geometryRow_of_fields geometryRowsJson3299 geometryRowsTyped3299 geometryRow3299_floorText
    geometryRow3299_simplexId_read geometryRow3299_vertexIds_read
    geometryRow3299_physicalVolume_read geometryRow3299_meanGap_read
    geometryRow3299_factorMaxima_read geometryRow3299_gapWeightedMeans_read
    geometryRow3299_jensenBound_read geometryRow3299_floor_text_read geometryRow3299_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3299_original_decoder_complete"
  err.flush

theorem geometryRow3299_shape :
    geometryRowsTyped3299.simplexId = 3299 ∧
    geometryRowsTyped3299.vertexIds.size = 9 ∧ geometryRowsTyped3299.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped3299.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped3299.factorMaxima.size = 10 ∧ geometryRowsTyped3299.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson3300 : SourceJson :=
  (SimplicesBlock412.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped3300 : GeometryRow :=
  { simplexId := 3300,
    vertexIds := #[139, 133, 114, 113, 99, 80, 49, 40, 3],
    physicalVolume := ((505499421893684142563886403649374411735027 : ℚ) / (22557813949440000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((146099 : ℚ) / (360000000 : ℚ)),
    factorMaxima := #[((10254 : ℚ) / (171875 : ℚ)), ((10254 : ℚ) / (171875 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((3370407 : ℚ) / (40000000 : ℚ)), ((207029 : ℚ) / (2968750 : ℚ)), ((207029 : ℚ) / (2968750 : ℚ)), ((1484407 : ℚ) / (54000000 : ℚ)), ((484403 : ℚ) / (18000000 : ℚ))],
    gapWeightedMeans := #[((830655219059 : ℚ) / (19186200000000 : ℚ)), ((211167660557 : ℚ) / (4796550000000 : ℚ)), ((750206936341 : ℚ) / (6395400000000 : ℚ)), ((635716841713 : ℚ) / (6395400000000 : ℚ)), ((585256773373 : ℚ) / (6395400000000 : ℚ)), ((8575303643 : ℚ) / (116280000000 : ℚ)), ((56161124839 : ℚ) / (852720000000 : ℚ)), ((161305649479 : ℚ) / (2558160000000 : ℚ)), ((26362112377 : ℚ) / (1199137500000 : ℚ)), ((20641083479 : ℚ) / (1065900000000 : ℚ))],
    jensenBound := ((86406078417902133400406748340228545703959863755941974394628244314619759890057966500000000000000000 : ℚ) / (629879148432912621453038040033173512032275028556452764329641490067742335408213560446117297443974276699302402467 : ℚ)),
    jensenFloorQ96 := (10868425856206847 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_simplexId_before"
  err.flush

theorem geometryRow3300_simplexId_read :
    geometryRowsJson3300.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped3300.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_vertexIds_before"
  err.flush

theorem geometryRow3300_vertexIds_read :
    geometryRowsJson3300.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped3300.vertexIds := by decide +kernel

noncomputable def geometryRow3300_physicalVolumeNumeratorChars : List Char := ['5', '0', '5', '4', '9', '9', '4', '2', '1', '8', '9', '3', '6', '8', '4', '1', '4', '2', '5', '6', '3', '8', '8', '6', '4', '0', '3', '6', '4', '9', '3', '7', '4', '4', '1', '1', '7', '3', '5', '0', '2', '7']
noncomputable def geometryRow3300_physicalVolumeDenominatorChars : List Char := ['2', '2', '5', '5', '7', '8', '1', '3', '9', '4', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3300_physicalVolumeText : String := String.ofList (geometryRow3300_physicalVolumeNumeratorChars ++ '/' :: geometryRow3300_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_physicalVolume_before_field"
  err.flush

theorem geometryRow3300_physicalVolume_field :
    geometryRowsJson3300.getObjVal? "physical_volume" = .ok (.str geometryRow3300_physicalVolumeText) := by rfl

theorem geometryRow3300_physicalVolume_numerator_no_slash :
    geometryRow3300_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3300_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow3300_physicalVolumeNumeratorChars = some (505499421893684142563886403649374411735027 : Int) := by decide +kernel

theorem geometryRow3300_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow3300_physicalVolumeDenominatorChars = some (22557813949440000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow3300_physicalVolume_denominator_nonzero : (22557813949440000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3300_physicalVolume_parse :
    parseRational geometryRow3300_physicalVolumeText = .ok geometryRowsTyped3300.physicalVolume :=
  original_rational_fraction_of_chars geometryRow3300_physicalVolumeNumeratorChars geometryRow3300_physicalVolumeDenominatorChars
    (505499421893684142563886403649374411735027 : Int) (22557813949440000000000000000000000000000000000000000000000000000 : Int)
    geometryRow3300_physicalVolume_numerator_no_slash geometryRow3300_physicalVolume_numerator_parse
    geometryRow3300_physicalVolume_denominator_parse geometryRow3300_physicalVolume_denominator_nonzero

theorem geometryRow3300_physicalVolume_read :
    rationalField geometryRowsJson3300 "physical_volume" = .ok geometryRowsTyped3300.physicalVolume :=
  original_rationalField_of_string geometryRowsJson3300 "physical_volume" geometryRow3300_physicalVolumeText
    geometryRowsTyped3300.physicalVolume geometryRow3300_physicalVolume_field geometryRow3300_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_physicalVolume_complete"
  err.flush

noncomputable def geometryRow3300_meanGapNumeratorChars : List Char := ['1', '4', '6', '0', '9', '9']
noncomputable def geometryRow3300_meanGapDenominatorChars : List Char := ['3', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3300_meanGapText : String := String.ofList (geometryRow3300_meanGapNumeratorChars ++ '/' :: geometryRow3300_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_meanGap_before_field"
  err.flush

theorem geometryRow3300_meanGap_field :
    geometryRowsJson3300.getObjVal? "mean_gap" = .ok (.str geometryRow3300_meanGapText) := by rfl

theorem geometryRow3300_meanGap_numerator_no_slash :
    geometryRow3300_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3300_meanGap_numerator_parse :
    SourceJson.intChars geometryRow3300_meanGapNumeratorChars = some (146099 : Int) := by decide +kernel

theorem geometryRow3300_meanGap_denominator_parse :
    SourceJson.intChars geometryRow3300_meanGapDenominatorChars = some (360000000 : Int) := by decide +kernel

theorem geometryRow3300_meanGap_denominator_nonzero : (360000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3300_meanGap_parse :
    parseRational geometryRow3300_meanGapText = .ok geometryRowsTyped3300.meanGap :=
  original_rational_fraction_of_chars geometryRow3300_meanGapNumeratorChars geometryRow3300_meanGapDenominatorChars
    (146099 : Int) (360000000 : Int)
    geometryRow3300_meanGap_numerator_no_slash geometryRow3300_meanGap_numerator_parse
    geometryRow3300_meanGap_denominator_parse geometryRow3300_meanGap_denominator_nonzero

theorem geometryRow3300_meanGap_read :
    rationalField geometryRowsJson3300 "mean_gap" = .ok geometryRowsTyped3300.meanGap :=
  original_rationalField_of_string geometryRowsJson3300 "mean_gap" geometryRow3300_meanGapText
    geometryRowsTyped3300.meanGap geometryRow3300_meanGap_field geometryRow3300_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_meanGap_complete"
  err.flush

noncomputable def geometryRow3300_jensenBoundNumeratorChars : List Char := ['8', '6', '4', '0', '6', '0', '7', '8', '4', '1', '7', '9', '0', '2', '1', '3', '3', '4', '0', '0', '4', '0', '6', '7', '4', '8', '3', '4', '0', '2', '2', '8', '5', '4', '5', '7', '0', '3', '9', '5', '9', '8', '6', '3', '7', '5', '5', '9', '4', '1', '9', '7', '4', '3', '9', '4', '6', '2', '8', '2', '4', '4', '3', '1', '4', '6', '1', '9', '7', '5', '9', '8', '9', '0', '0', '5', '7', '9', '6', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3300_jensenBoundDenominatorChars : List Char := ['6', '2', '9', '8', '7', '9', '1', '4', '8', '4', '3', '2', '9', '1', '2', '6', '2', '1', '4', '5', '3', '0', '3', '8', '0', '4', '0', '0', '3', '3', '1', '7', '3', '5', '1', '2', '0', '3', '2', '2', '7', '5', '0', '2', '8', '5', '5', '6', '4', '5', '2', '7', '6', '4', '3', '2', '9', '6', '4', '1', '4', '9', '0', '0', '6', '7', '7', '4', '2', '3', '3', '5', '4', '0', '8', '2', '1', '3', '5', '6', '0', '4', '4', '6', '1', '1', '7', '2', '9', '7', '4', '4', '3', '9', '7', '4', '2', '7', '6', '6', '9', '9', '3', '0', '2', '4', '0', '2', '4', '6', '7']
noncomputable def geometryRow3300_jensenBoundText : String := String.ofList (geometryRow3300_jensenBoundNumeratorChars ++ '/' :: geometryRow3300_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_jensenBound_before_field"
  err.flush

theorem geometryRow3300_jensenBound_field :
    geometryRowsJson3300.getObjVal? "jensen_bound" = .ok (.str geometryRow3300_jensenBoundText) := by rfl

theorem geometryRow3300_jensenBound_numerator_no_slash :
    geometryRow3300_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3300_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow3300_jensenBoundNumeratorChars = some (86406078417902133400406748340228545703959863755941974394628244314619759890057966500000000000000000 : Int) := by decide +kernel

theorem geometryRow3300_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow3300_jensenBoundDenominatorChars = some (629879148432912621453038040033173512032275028556452764329641490067742335408213560446117297443974276699302402467 : Int) := by decide +kernel

theorem geometryRow3300_jensenBound_denominator_nonzero : (629879148432912621453038040033173512032275028556452764329641490067742335408213560446117297443974276699302402467 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3300_jensenBound_parse :
    parseRational geometryRow3300_jensenBoundText = .ok geometryRowsTyped3300.jensenBound :=
  original_rational_fraction_of_chars geometryRow3300_jensenBoundNumeratorChars geometryRow3300_jensenBoundDenominatorChars
    (86406078417902133400406748340228545703959863755941974394628244314619759890057966500000000000000000 : Int) (629879148432912621453038040033173512032275028556452764329641490067742335408213560446117297443974276699302402467 : Int)
    geometryRow3300_jensenBound_numerator_no_slash geometryRow3300_jensenBound_numerator_parse
    geometryRow3300_jensenBound_denominator_parse geometryRow3300_jensenBound_denominator_nonzero

theorem geometryRow3300_jensenBound_read :
    rationalField geometryRowsJson3300 "jensen_bound" = .ok geometryRowsTyped3300.jensenBound :=
  original_rationalField_of_string geometryRowsJson3300 "jensen_bound" geometryRow3300_jensenBoundText
    geometryRowsTyped3300.jensenBound geometryRow3300_jensenBound_field geometryRow3300_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_factorMaxima_before"
  err.flush

theorem geometryRow3300_factorMaxima_read :
    rationalArrayField geometryRowsJson3300 "factor_maxima" = .ok geometryRowsTyped3300.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_gapWeightedMeans_before"
  err.flush

theorem geometryRow3300_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson3300 "gap_weighted_means" = .ok geometryRowsTyped3300.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow3300_floorChars : List Char := ['1', '0', '8', '6', '8', '4', '2', '5', '8', '5', '6', '2', '0', '6', '8', '4', '7']
noncomputable def geometryRow3300_floorText : String := String.ofList geometryRow3300_floorChars

theorem geometryRow3300_floor_text_read :
    geometryRowsJson3300.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow3300_floorText := by rfl

theorem geometryRow3300_floor_chars_parse :
    SourceJson.intChars geometryRow3300_floorChars = some (10868425856206847 : Int) := by decide +kernel

theorem geometryRow3300_floor_parse :
    parseInteger geometryRow3300_floorText = .ok geometryRowsTyped3300.jensenFloorQ96 := by
  simp only [geometryRow3300_floorText, parseInteger, String.toList_ofList, geometryRow3300_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_3300 :
    decodeGeometryRow geometryRowsJson3300 = .ok geometryRowsTyped3300 :=
  original_geometryRow_of_fields geometryRowsJson3300 geometryRowsTyped3300 geometryRow3300_floorText
    geometryRow3300_simplexId_read geometryRow3300_vertexIds_read
    geometryRow3300_physicalVolume_read geometryRow3300_meanGap_read
    geometryRow3300_factorMaxima_read geometryRow3300_gapWeightedMeans_read
    geometryRow3300_jensenBound_read geometryRow3300_floor_text_read geometryRow3300_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3300_original_decoder_complete"
  err.flush

theorem geometryRow3300_shape :
    geometryRowsTyped3300.simplexId = 3300 ∧
    geometryRowsTyped3300.vertexIds.size = 9 ∧ geometryRowsTyped3300.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped3300.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped3300.factorMaxima.size = 10 ∧ geometryRowsTyped3300.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson3301 : SourceJson :=
  (SimplicesBlock412.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped3301 : GeometryRow :=
  { simplexId := 3301,
    vertexIds := #[139, 133, 114, 113, 99, 80, 71, 40, 3],
    physicalVolume := ((2273204443944562929904117524834223667791733 : ℚ) / (112909699768320000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((146099 : ℚ) / (360000000 : ℚ)),
    factorMaxima := #[((65627 : ℚ) / (1200000 : ℚ)), ((65627 : ℚ) / (1200000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((3370407 : ℚ) / (40000000 : ℚ)), ((207029 : ℚ) / (2968750 : ℚ)), ((207029 : ℚ) / (2968750 : ℚ)), ((1484407 : ℚ) / (54000000 : ℚ)), ((484403 : ℚ) / (18000000 : ℚ))],
    gapWeightedMeans := #[((238685085823 : ℚ) / (5668650000000 : ℚ)), ((971304025219 : ℚ) / (22674600000000 : ℚ)), ((889249690613 : ℚ) / (7558200000000 : ℚ)), ((29112957409 : ℚ) / (290700000000 : ℚ)), ((26819317939 : ℚ) / (290700000000 : ℚ)), ((113204716979 : ℚ) / (1511640000000 : ℚ)), ((66243096821 : ℚ) / (1007760000000 : ℚ)), ((190246524509 : ℚ) / (3023280000000 : ℚ)), ((489502547021 : ℚ) / (22674600000000 : ℚ)), ((47790122999 : ℚ) / (2519400000000 : ℚ))],
    jensenBound := ((4941495007081328513983042357517182747764819416977263353966965840703053583587008100500000000000000000 : ℚ) / (37605491960624184260236858530327811241975020251853162142792367918784761921467410237318931524035295070711212640533 : ℚ)),
    jensenFloorQ96 := (10410861527736466 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_simplexId_before"
  err.flush

theorem geometryRow3301_simplexId_read :
    geometryRowsJson3301.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped3301.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_vertexIds_before"
  err.flush

theorem geometryRow3301_vertexIds_read :
    geometryRowsJson3301.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped3301.vertexIds := by decide +kernel

noncomputable def geometryRow3301_physicalVolumeNumeratorChars : List Char := ['2', '2', '7', '3', '2', '0', '4', '4', '4', '3', '9', '4', '4', '5', '6', '2', '9', '2', '9', '9', '0', '4', '1', '1', '7', '5', '2', '4', '8', '3', '4', '2', '2', '3', '6', '6', '7', '7', '9', '1', '7', '3', '3']
noncomputable def geometryRow3301_physicalVolumeDenominatorChars : List Char := ['1', '1', '2', '9', '0', '9', '6', '9', '9', '7', '6', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3301_physicalVolumeText : String := String.ofList (geometryRow3301_physicalVolumeNumeratorChars ++ '/' :: geometryRow3301_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_physicalVolume_before_field"
  err.flush

theorem geometryRow3301_physicalVolume_field :
    geometryRowsJson3301.getObjVal? "physical_volume" = .ok (.str geometryRow3301_physicalVolumeText) := by rfl

theorem geometryRow3301_physicalVolume_numerator_no_slash :
    geometryRow3301_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3301_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow3301_physicalVolumeNumeratorChars = some (2273204443944562929904117524834223667791733 : Int) := by decide +kernel

theorem geometryRow3301_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow3301_physicalVolumeDenominatorChars = some (112909699768320000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow3301_physicalVolume_denominator_nonzero : (112909699768320000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3301_physicalVolume_parse :
    parseRational geometryRow3301_physicalVolumeText = .ok geometryRowsTyped3301.physicalVolume :=
  original_rational_fraction_of_chars geometryRow3301_physicalVolumeNumeratorChars geometryRow3301_physicalVolumeDenominatorChars
    (2273204443944562929904117524834223667791733 : Int) (112909699768320000000000000000000000000000000000000000000000000000 : Int)
    geometryRow3301_physicalVolume_numerator_no_slash geometryRow3301_physicalVolume_numerator_parse
    geometryRow3301_physicalVolume_denominator_parse geometryRow3301_physicalVolume_denominator_nonzero

theorem geometryRow3301_physicalVolume_read :
    rationalField geometryRowsJson3301 "physical_volume" = .ok geometryRowsTyped3301.physicalVolume :=
  original_rationalField_of_string geometryRowsJson3301 "physical_volume" geometryRow3301_physicalVolumeText
    geometryRowsTyped3301.physicalVolume geometryRow3301_physicalVolume_field geometryRow3301_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_physicalVolume_complete"
  err.flush

noncomputable def geometryRow3301_meanGapNumeratorChars : List Char := ['1', '4', '6', '0', '9', '9']
noncomputable def geometryRow3301_meanGapDenominatorChars : List Char := ['3', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3301_meanGapText : String := String.ofList (geometryRow3301_meanGapNumeratorChars ++ '/' :: geometryRow3301_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_meanGap_before_field"
  err.flush

theorem geometryRow3301_meanGap_field :
    geometryRowsJson3301.getObjVal? "mean_gap" = .ok (.str geometryRow3301_meanGapText) := by rfl

theorem geometryRow3301_meanGap_numerator_no_slash :
    geometryRow3301_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3301_meanGap_numerator_parse :
    SourceJson.intChars geometryRow3301_meanGapNumeratorChars = some (146099 : Int) := by decide +kernel

theorem geometryRow3301_meanGap_denominator_parse :
    SourceJson.intChars geometryRow3301_meanGapDenominatorChars = some (360000000 : Int) := by decide +kernel

theorem geometryRow3301_meanGap_denominator_nonzero : (360000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3301_meanGap_parse :
    parseRational geometryRow3301_meanGapText = .ok geometryRowsTyped3301.meanGap :=
  original_rational_fraction_of_chars geometryRow3301_meanGapNumeratorChars geometryRow3301_meanGapDenominatorChars
    (146099 : Int) (360000000 : Int)
    geometryRow3301_meanGap_numerator_no_slash geometryRow3301_meanGap_numerator_parse
    geometryRow3301_meanGap_denominator_parse geometryRow3301_meanGap_denominator_nonzero

theorem geometryRow3301_meanGap_read :
    rationalField geometryRowsJson3301 "mean_gap" = .ok geometryRowsTyped3301.meanGap :=
  original_rationalField_of_string geometryRowsJson3301 "mean_gap" geometryRow3301_meanGapText
    geometryRowsTyped3301.meanGap geometryRow3301_meanGap_field geometryRow3301_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_meanGap_complete"
  err.flush

noncomputable def geometryRow3301_jensenBoundNumeratorChars : List Char := ['4', '9', '4', '1', '4', '9', '5', '0', '0', '7', '0', '8', '1', '3', '2', '8', '5', '1', '3', '9', '8', '3', '0', '4', '2', '3', '5', '7', '5', '1', '7', '1', '8', '2', '7', '4', '7', '7', '6', '4', '8', '1', '9', '4', '1', '6', '9', '7', '7', '2', '6', '3', '3', '5', '3', '9', '6', '6', '9', '6', '5', '8', '4', '0', '7', '0', '3', '0', '5', '3', '5', '8', '3', '5', '8', '7', '0', '0', '8', '1', '0', '0', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3301_jensenBoundDenominatorChars : List Char := ['3', '7', '6', '0', '5', '4', '9', '1', '9', '6', '0', '6', '2', '4', '1', '8', '4', '2', '6', '0', '2', '3', '6', '8', '5', '8', '5', '3', '0', '3', '2', '7', '8', '1', '1', '2', '4', '1', '9', '7', '5', '0', '2', '0', '2', '5', '1', '8', '5', '3', '1', '6', '2', '1', '4', '2', '7', '9', '2', '3', '6', '7', '9', '1', '8', '7', '8', '4', '7', '6', '1', '9', '2', '1', '4', '6', '7', '4', '1', '0', '2', '3', '7', '3', '1', '8', '9', '3', '1', '5', '2', '4', '0', '3', '5', '2', '9', '5', '0', '7', '0', '7', '1', '1', '2', '1', '2', '6', '4', '0', '5', '3', '3']
noncomputable def geometryRow3301_jensenBoundText : String := String.ofList (geometryRow3301_jensenBoundNumeratorChars ++ '/' :: geometryRow3301_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_jensenBound_before_field"
  err.flush

theorem geometryRow3301_jensenBound_field :
    geometryRowsJson3301.getObjVal? "jensen_bound" = .ok (.str geometryRow3301_jensenBoundText) := by rfl

theorem geometryRow3301_jensenBound_numerator_no_slash :
    geometryRow3301_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3301_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow3301_jensenBoundNumeratorChars = some (4941495007081328513983042357517182747764819416977263353966965840703053583587008100500000000000000000 : Int) := by decide +kernel

theorem geometryRow3301_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow3301_jensenBoundDenominatorChars = some (37605491960624184260236858530327811241975020251853162142792367918784761921467410237318931524035295070711212640533 : Int) := by decide +kernel

theorem geometryRow3301_jensenBound_denominator_nonzero : (37605491960624184260236858530327811241975020251853162142792367918784761921467410237318931524035295070711212640533 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3301_jensenBound_parse :
    parseRational geometryRow3301_jensenBoundText = .ok geometryRowsTyped3301.jensenBound :=
  original_rational_fraction_of_chars geometryRow3301_jensenBoundNumeratorChars geometryRow3301_jensenBoundDenominatorChars
    (4941495007081328513983042357517182747764819416977263353966965840703053583587008100500000000000000000 : Int) (37605491960624184260236858530327811241975020251853162142792367918784761921467410237318931524035295070711212640533 : Int)
    geometryRow3301_jensenBound_numerator_no_slash geometryRow3301_jensenBound_numerator_parse
    geometryRow3301_jensenBound_denominator_parse geometryRow3301_jensenBound_denominator_nonzero

theorem geometryRow3301_jensenBound_read :
    rationalField geometryRowsJson3301 "jensen_bound" = .ok geometryRowsTyped3301.jensenBound :=
  original_rationalField_of_string geometryRowsJson3301 "jensen_bound" geometryRow3301_jensenBoundText
    geometryRowsTyped3301.jensenBound geometryRow3301_jensenBound_field geometryRow3301_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_factorMaxima_before"
  err.flush

theorem geometryRow3301_factorMaxima_read :
    rationalArrayField geometryRowsJson3301 "factor_maxima" = .ok geometryRowsTyped3301.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_gapWeightedMeans_before"
  err.flush

theorem geometryRow3301_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson3301 "gap_weighted_means" = .ok geometryRowsTyped3301.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow3301_floorChars : List Char := ['1', '0', '4', '1', '0', '8', '6', '1', '5', '2', '7', '7', '3', '6', '4', '6', '6']
noncomputable def geometryRow3301_floorText : String := String.ofList geometryRow3301_floorChars

theorem geometryRow3301_floor_text_read :
    geometryRowsJson3301.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow3301_floorText := by rfl

theorem geometryRow3301_floor_chars_parse :
    SourceJson.intChars geometryRow3301_floorChars = some (10410861527736466 : Int) := by decide +kernel

theorem geometryRow3301_floor_parse :
    parseInteger geometryRow3301_floorText = .ok geometryRowsTyped3301.jensenFloorQ96 := by
  simp only [geometryRow3301_floorText, parseInteger, String.toList_ofList, geometryRow3301_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_3301 :
    decodeGeometryRow geometryRowsJson3301 = .ok geometryRowsTyped3301 :=
  original_geometryRow_of_fields geometryRowsJson3301 geometryRowsTyped3301 geometryRow3301_floorText
    geometryRow3301_simplexId_read geometryRow3301_vertexIds_read
    geometryRow3301_physicalVolume_read geometryRow3301_meanGap_read
    geometryRow3301_factorMaxima_read geometryRow3301_gapWeightedMeans_read
    geometryRow3301_jensenBound_read geometryRow3301_floor_text_read geometryRow3301_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3301_original_decoder_complete"
  err.flush

theorem geometryRow3301_shape :
    geometryRowsTyped3301.simplexId = 3301 ∧
    geometryRowsTyped3301.vertexIds.size = 9 ∧ geometryRowsTyped3301.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped3301.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped3301.factorMaxima.size = 10 ∧ geometryRowsTyped3301.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson3302 : SourceJson :=
  (SimplicesBlock412.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped3302 : GeometryRow :=
  { simplexId := 3302,
    vertexIds := #[139, 133, 114, 113, 99, 91, 62, 44, 41],
    physicalVolume := ((1122643493297998164591945784495519327 : ℚ) / (313445046878208000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((16810899269 : ℚ) / (6843420000000 : ℚ)),
    factorMaxima := #[((8953073 : ℚ) / (228000000 : ℚ)), ((1859329 : ℚ) / (46000000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((3499989 : ℚ) / (47500000 : ℚ)), ((828137 : ℚ) / (12000000 : ℚ)), ((25671743 : ℚ) / (380000000 : ℚ)), ((49 : ℚ) / (1472 : ℚ)), ((49 : ℚ) / (1472 : ℚ))],
    gapWeightedMeans := #[((4514183007233335528275167 : ℚ) / (136902412687797376200000000 : ℚ)), ((4898073505483930964040329 : ℚ) / (136902412687797376200000000 : ℚ)), ((9425544824380768338671 : ℚ) / (79225933268401259375000 : ℚ)), ((236185601461567588422199 : ℚ) / (2401796713821006600000000 : ℚ)), ((4127470496937355732120441 : ℚ) / (45634137562599125400000000 : ℚ)), ((177340377217468682458797 : ℚ) / (2535229864588840300000000 : ℚ)), ((6000024323055603376126097 : ℚ) / (91268275125198250800000000 : ℚ)), ((5743942379963221324385407 : ℚ) / (91268275125198250800000000 : ℚ)), ((3951404620331875898090779 : ℚ) / (136902412687797376200000000 : ℚ)), ((1197605658182393871813623 : ℚ) / (45634137562599125400000000 : ℚ))],
    jensenBound := ((251889798090958595368909665640691299968514584660639121946959560771593808817799619047463117428594182046280732716644192641734193402651904741857037405540257794239097147686840150490334896043396076166190368349609375000000000000000000 : ℚ) / (1958678337817469173847616908479452501428704160317680304355559786696213698779297288844680440511355384662998157215119904004718231280036114636843094600541349390711769441498471056424322302949699106485113876512659942085487069626471131204442205339 : ℚ)),
    jensenFloorQ96 := (10188893946248097 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_simplexId_before"
  err.flush

theorem geometryRow3302_simplexId_read :
    geometryRowsJson3302.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped3302.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_vertexIds_before"
  err.flush

theorem geometryRow3302_vertexIds_read :
    geometryRowsJson3302.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped3302.vertexIds := by decide +kernel

noncomputable def geometryRow3302_physicalVolumeNumeratorChars : List Char := ['1', '1', '2', '2', '6', '4', '3', '4', '9', '3', '2', '9', '7', '9', '9', '8', '1', '6', '4', '5', '9', '1', '9', '4', '5', '7', '8', '4', '4', '9', '5', '5', '1', '9', '3', '2', '7']
noncomputable def geometryRow3302_physicalVolumeDenominatorChars : List Char := ['3', '1', '3', '4', '4', '5', '0', '4', '6', '8', '7', '8', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3302_physicalVolumeText : String := String.ofList (geometryRow3302_physicalVolumeNumeratorChars ++ '/' :: geometryRow3302_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_physicalVolume_before_field"
  err.flush

theorem geometryRow3302_physicalVolume_field :
    geometryRowsJson3302.getObjVal? "physical_volume" = .ok (.str geometryRow3302_physicalVolumeText) := by rfl

theorem geometryRow3302_physicalVolume_numerator_no_slash :
    geometryRow3302_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3302_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow3302_physicalVolumeNumeratorChars = some (1122643493297998164591945784495519327 : Int) := by decide +kernel

theorem geometryRow3302_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow3302_physicalVolumeDenominatorChars = some (313445046878208000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow3302_physicalVolume_denominator_nonzero : (313445046878208000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3302_physicalVolume_parse :
    parseRational geometryRow3302_physicalVolumeText = .ok geometryRowsTyped3302.physicalVolume :=
  original_rational_fraction_of_chars geometryRow3302_physicalVolumeNumeratorChars geometryRow3302_physicalVolumeDenominatorChars
    (1122643493297998164591945784495519327 : Int) (313445046878208000000000000000000000000000000000000000000000 : Int)
    geometryRow3302_physicalVolume_numerator_no_slash geometryRow3302_physicalVolume_numerator_parse
    geometryRow3302_physicalVolume_denominator_parse geometryRow3302_physicalVolume_denominator_nonzero

theorem geometryRow3302_physicalVolume_read :
    rationalField geometryRowsJson3302 "physical_volume" = .ok geometryRowsTyped3302.physicalVolume :=
  original_rationalField_of_string geometryRowsJson3302 "physical_volume" geometryRow3302_physicalVolumeText
    geometryRowsTyped3302.physicalVolume geometryRow3302_physicalVolume_field geometryRow3302_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_physicalVolume_complete"
  err.flush

noncomputable def geometryRow3302_meanGapNumeratorChars : List Char := ['1', '6', '8', '1', '0', '8', '9', '9', '2', '6', '9']
noncomputable def geometryRow3302_meanGapDenominatorChars : List Char := ['6', '8', '4', '3', '4', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3302_meanGapText : String := String.ofList (geometryRow3302_meanGapNumeratorChars ++ '/' :: geometryRow3302_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_meanGap_before_field"
  err.flush

theorem geometryRow3302_meanGap_field :
    geometryRowsJson3302.getObjVal? "mean_gap" = .ok (.str geometryRow3302_meanGapText) := by rfl

theorem geometryRow3302_meanGap_numerator_no_slash :
    geometryRow3302_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3302_meanGap_numerator_parse :
    SourceJson.intChars geometryRow3302_meanGapNumeratorChars = some (16810899269 : Int) := by decide +kernel

theorem geometryRow3302_meanGap_denominator_parse :
    SourceJson.intChars geometryRow3302_meanGapDenominatorChars = some (6843420000000 : Int) := by decide +kernel

theorem geometryRow3302_meanGap_denominator_nonzero : (6843420000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3302_meanGap_parse :
    parseRational geometryRow3302_meanGapText = .ok geometryRowsTyped3302.meanGap :=
  original_rational_fraction_of_chars geometryRow3302_meanGapNumeratorChars geometryRow3302_meanGapDenominatorChars
    (16810899269 : Int) (6843420000000 : Int)
    geometryRow3302_meanGap_numerator_no_slash geometryRow3302_meanGap_numerator_parse
    geometryRow3302_meanGap_denominator_parse geometryRow3302_meanGap_denominator_nonzero

theorem geometryRow3302_meanGap_read :
    rationalField geometryRowsJson3302 "mean_gap" = .ok geometryRowsTyped3302.meanGap :=
  original_rationalField_of_string geometryRowsJson3302 "mean_gap" geometryRow3302_meanGapText
    geometryRowsTyped3302.meanGap geometryRow3302_meanGap_field geometryRow3302_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_meanGap_complete"
  err.flush

noncomputable def geometryRow3302_jensenBoundNumeratorChars : List Char := ['2', '5', '1', '8', '8', '9', '7', '9', '8', '0', '9', '0', '9', '5', '8', '5', '9', '5', '3', '6', '8', '9', '0', '9', '6', '6', '5', '6', '4', '0', '6', '9', '1', '2', '9', '9', '9', '6', '8', '5', '1', '4', '5', '8', '4', '6', '6', '0', '6', '3', '9', '1', '2', '1', '9', '4', '6', '9', '5', '9', '5', '6', '0', '7', '7', '1', '5', '9', '3', '8', '0', '8', '8', '1', '7', '7', '9', '9', '6', '1', '9', '0', '4', '7', '4', '6', '3', '1', '1', '7', '4', '2', '8', '5', '9', '4', '1', '8', '2', '0', '4', '6', '2', '8', '0', '7', '3', '2', '7', '1', '6', '6', '4', '4', '1', '9', '2', '6', '4', '1', '7', '3', '4', '1', '9', '3', '4', '0', '2', '6', '5', '1', '9', '0', '4', '7', '4', '1', '8', '5', '7', '0', '3', '7', '4', '0', '5', '5', '4', '0', '2', '5', '7', '7', '9', '4', '2', '3', '9', '0', '9', '7', '1', '4', '7', '6', '8', '6', '8', '4', '0', '1', '5', '0', '4', '9', '0', '3', '3', '4', '8', '9', '6', '0', '4', '3', '3', '9', '6', '0', '7', '6', '1', '6', '6', '1', '9', '0', '3', '6', '8', '3', '4', '9', '6', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3302_jensenBoundDenominatorChars : List Char := ['1', '9', '5', '8', '6', '7', '8', '3', '3', '7', '8', '1', '7', '4', '6', '9', '1', '7', '3', '8', '4', '7', '6', '1', '6', '9', '0', '8', '4', '7', '9', '4', '5', '2', '5', '0', '1', '4', '2', '8', '7', '0', '4', '1', '6', '0', '3', '1', '7', '6', '8', '0', '3', '0', '4', '3', '5', '5', '5', '5', '9', '7', '8', '6', '6', '9', '6', '2', '1', '3', '6', '9', '8', '7', '7', '9', '2', '9', '7', '2', '8', '8', '8', '4', '4', '6', '8', '0', '4', '4', '0', '5', '1', '1', '3', '5', '5', '3', '8', '4', '6', '6', '2', '9', '9', '8', '1', '5', '7', '2', '1', '5', '1', '1', '9', '9', '0', '4', '0', '0', '4', '7', '1', '8', '2', '3', '1', '2', '8', '0', '0', '3', '6', '1', '1', '4', '6', '3', '6', '8', '4', '3', '0', '9', '4', '6', '0', '0', '5', '4', '1', '3', '4', '9', '3', '9', '0', '7', '1', '1', '7', '6', '9', '4', '4', '1', '4', '9', '8', '4', '7', '1', '0', '5', '6', '4', '2', '4', '3', '2', '2', '3', '0', '2', '9', '4', '9', '6', '9', '9', '1', '0', '6', '4', '8', '5', '1', '1', '3', '8', '7', '6', '5', '1', '2', '6', '5', '9', '9', '4', '2', '0', '8', '5', '4', '8', '7', '0', '6', '9', '6', '2', '6', '4', '7', '1', '1', '3', '1', '2', '0', '4', '4', '4', '2', '2', '0', '5', '3', '3', '9']
noncomputable def geometryRow3302_jensenBoundText : String := String.ofList (geometryRow3302_jensenBoundNumeratorChars ++ '/' :: geometryRow3302_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_jensenBound_before_field"
  err.flush

theorem geometryRow3302_jensenBound_field :
    geometryRowsJson3302.getObjVal? "jensen_bound" = .ok (.str geometryRow3302_jensenBoundText) := by rfl

theorem geometryRow3302_jensenBound_numerator_no_slash :
    geometryRow3302_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3302_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow3302_jensenBoundNumeratorChars = some (251889798090958595368909665640691299968514584660639121946959560771593808817799619047463117428594182046280732716644192641734193402651904741857037405540257794239097147686840150490334896043396076166190368349609375000000000000000000 : Int) := by decide +kernel

theorem geometryRow3302_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow3302_jensenBoundDenominatorChars = some (1958678337817469173847616908479452501428704160317680304355559786696213698779297288844680440511355384662998157215119904004718231280036114636843094600541349390711769441498471056424322302949699106485113876512659942085487069626471131204442205339 : Int) := by decide +kernel

theorem geometryRow3302_jensenBound_denominator_nonzero : (1958678337817469173847616908479452501428704160317680304355559786696213698779297288844680440511355384662998157215119904004718231280036114636843094600541349390711769441498471056424322302949699106485113876512659942085487069626471131204442205339 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3302_jensenBound_parse :
    parseRational geometryRow3302_jensenBoundText = .ok geometryRowsTyped3302.jensenBound :=
  original_rational_fraction_of_chars geometryRow3302_jensenBoundNumeratorChars geometryRow3302_jensenBoundDenominatorChars
    (251889798090958595368909665640691299968514584660639121946959560771593808817799619047463117428594182046280732716644192641734193402651904741857037405540257794239097147686840150490334896043396076166190368349609375000000000000000000 : Int) (1958678337817469173847616908479452501428704160317680304355559786696213698779297288844680440511355384662998157215119904004718231280036114636843094600541349390711769441498471056424322302949699106485113876512659942085487069626471131204442205339 : Int)
    geometryRow3302_jensenBound_numerator_no_slash geometryRow3302_jensenBound_numerator_parse
    geometryRow3302_jensenBound_denominator_parse geometryRow3302_jensenBound_denominator_nonzero

theorem geometryRow3302_jensenBound_read :
    rationalField geometryRowsJson3302 "jensen_bound" = .ok geometryRowsTyped3302.jensenBound :=
  original_rationalField_of_string geometryRowsJson3302 "jensen_bound" geometryRow3302_jensenBoundText
    geometryRowsTyped3302.jensenBound geometryRow3302_jensenBound_field geometryRow3302_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_factorMaxima_before"
  err.flush

theorem geometryRow3302_factorMaxima_read :
    rationalArrayField geometryRowsJson3302 "factor_maxima" = .ok geometryRowsTyped3302.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_gapWeightedMeans_before"
  err.flush

theorem geometryRow3302_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson3302 "gap_weighted_means" = .ok geometryRowsTyped3302.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow3302_floorChars : List Char := ['1', '0', '1', '8', '8', '8', '9', '3', '9', '4', '6', '2', '4', '8', '0', '9', '7']
noncomputable def geometryRow3302_floorText : String := String.ofList geometryRow3302_floorChars

theorem geometryRow3302_floor_text_read :
    geometryRowsJson3302.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow3302_floorText := by rfl

theorem geometryRow3302_floor_chars_parse :
    SourceJson.intChars geometryRow3302_floorChars = some (10188893946248097 : Int) := by decide +kernel

theorem geometryRow3302_floor_parse :
    parseInteger geometryRow3302_floorText = .ok geometryRowsTyped3302.jensenFloorQ96 := by
  simp only [geometryRow3302_floorText, parseInteger, String.toList_ofList, geometryRow3302_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_3302 :
    decodeGeometryRow geometryRowsJson3302 = .ok geometryRowsTyped3302 :=
  original_geometryRow_of_fields geometryRowsJson3302 geometryRowsTyped3302 geometryRow3302_floorText
    geometryRow3302_simplexId_read geometryRow3302_vertexIds_read
    geometryRow3302_physicalVolume_read geometryRow3302_meanGap_read
    geometryRow3302_factorMaxima_read geometryRow3302_gapWeightedMeans_read
    geometryRow3302_jensenBound_read geometryRow3302_floor_text_read geometryRow3302_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3302_original_decoder_complete"
  err.flush

theorem geometryRow3302_shape :
    geometryRowsTyped3302.simplexId = 3302 ∧
    geometryRowsTyped3302.vertexIds.size = 9 ∧ geometryRowsTyped3302.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped3302.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped3302.factorMaxima.size = 10 ∧ geometryRowsTyped3302.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson3303 : SourceJson :=
  (SimplicesBlock412.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped3303 : GeometryRow :=
  { simplexId := 3303,
    vertexIds := #[139, 133, 114, 113, 99, 91, 62, 57, 41],
    physicalVolume := ((1717925542654040290406814073785310761881 : ℚ) / (1300919384016000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((130592302061 : ℚ) / (58615380000000 : ℚ)),
    factorMaxima := #[((8953073 : ℚ) / (228000000 : ℚ)), ((8953073 : ℚ) / (228000000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((3499989 : ℚ) / (47500000 : ℚ)), ((828137 : ℚ) / (12000000 : ℚ)), ((6718717 : ℚ) / (98500000 : ℚ)), ((11 : ℚ) / (336 : ℚ)), ((11 : ℚ) / (336 : ℚ))],
    gapWeightedMeans := #[((42609189719780791743489251 : ℚ) / (1301301959764650690600000000 : ℚ)), ((45906756397662200181227357 : ℚ) / (1301301959764650690600000000 : ℚ)), ((5743684197261358863211297 : ℚ) / (48196368880172247800000000 : ℚ)), ((1121279854198566707195711 : ℚ) / (11414929471619742900000000 : ℚ)), ((19593092864846408799679799 : ℚ) / (216883659960775115100000000 : ℚ)), ((3351223406836652077983667 : ℚ) / (48196368880172247800000000 : ℚ)), ((28736031026839983149496793 : ℚ) / (433767319921550230200000000 : ℚ)), ((6879739986821964225325577 : ℚ) / (108441829980387557550000000 : ℚ)), ((37259798110020397416340207 : ℚ) / (1301301959764650690600000000 : ℚ)), ((11283768635700810287750459 : ℚ) / (433767319921550230200000000 : ℚ))],
    jensenBound := ((149104059982338881084689365806939401075837853728563832605519633657836148110822259336851311564962112755862486477666990450654797112138939688809965773766521713025290871553915082236235332865164066910613128385169234776085840000000000000000000000 : ℚ) / (3368840059620744620681490997751306362395963568837130923787834459616813205478647199724460065490534705401092969594667561793370426279396380027017730267893479190405494646161047210393870453634194529354279543010363943724312847671543156055454382330533089855889 : ℚ)),
    jensenFloorQ96 := (3506619633686992 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_simplexId_before"
  err.flush

theorem geometryRow3303_simplexId_read :
    geometryRowsJson3303.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped3303.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_vertexIds_before"
  err.flush

theorem geometryRow3303_vertexIds_read :
    geometryRowsJson3303.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped3303.vertexIds := by decide +kernel

noncomputable def geometryRow3303_physicalVolumeNumeratorChars : List Char := ['1', '7', '1', '7', '9', '2', '5', '5', '4', '2', '6', '5', '4', '0', '4', '0', '2', '9', '0', '4', '0', '6', '8', '1', '4', '0', '7', '3', '7', '8', '5', '3', '1', '0', '7', '6', '1', '8', '8', '1']
noncomputable def geometryRow3303_physicalVolumeDenominatorChars : List Char := ['1', '3', '0', '0', '9', '1', '9', '3', '8', '4', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3303_physicalVolumeText : String := String.ofList (geometryRow3303_physicalVolumeNumeratorChars ++ '/' :: geometryRow3303_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_physicalVolume_before_field"
  err.flush

theorem geometryRow3303_physicalVolume_field :
    geometryRowsJson3303.getObjVal? "physical_volume" = .ok (.str geometryRow3303_physicalVolumeText) := by rfl

theorem geometryRow3303_physicalVolume_numerator_no_slash :
    geometryRow3303_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3303_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow3303_physicalVolumeNumeratorChars = some (1717925542654040290406814073785310761881 : Int) := by decide +kernel

theorem geometryRow3303_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow3303_physicalVolumeDenominatorChars = some (1300919384016000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow3303_physicalVolume_denominator_nonzero : (1300919384016000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3303_physicalVolume_parse :
    parseRational geometryRow3303_physicalVolumeText = .ok geometryRowsTyped3303.physicalVolume :=
  original_rational_fraction_of_chars geometryRow3303_physicalVolumeNumeratorChars geometryRow3303_physicalVolumeDenominatorChars
    (1717925542654040290406814073785310761881 : Int) (1300919384016000000000000000000000000000000000000000000000000000 : Int)
    geometryRow3303_physicalVolume_numerator_no_slash geometryRow3303_physicalVolume_numerator_parse
    geometryRow3303_physicalVolume_denominator_parse geometryRow3303_physicalVolume_denominator_nonzero

theorem geometryRow3303_physicalVolume_read :
    rationalField geometryRowsJson3303 "physical_volume" = .ok geometryRowsTyped3303.physicalVolume :=
  original_rationalField_of_string geometryRowsJson3303 "physical_volume" geometryRow3303_physicalVolumeText
    geometryRowsTyped3303.physicalVolume geometryRow3303_physicalVolume_field geometryRow3303_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_physicalVolume_complete"
  err.flush

noncomputable def geometryRow3303_meanGapNumeratorChars : List Char := ['1', '3', '0', '5', '9', '2', '3', '0', '2', '0', '6', '1']
noncomputable def geometryRow3303_meanGapDenominatorChars : List Char := ['5', '8', '6', '1', '5', '3', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3303_meanGapText : String := String.ofList (geometryRow3303_meanGapNumeratorChars ++ '/' :: geometryRow3303_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_meanGap_before_field"
  err.flush

theorem geometryRow3303_meanGap_field :
    geometryRowsJson3303.getObjVal? "mean_gap" = .ok (.str geometryRow3303_meanGapText) := by rfl

theorem geometryRow3303_meanGap_numerator_no_slash :
    geometryRow3303_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3303_meanGap_numerator_parse :
    SourceJson.intChars geometryRow3303_meanGapNumeratorChars = some (130592302061 : Int) := by decide +kernel

theorem geometryRow3303_meanGap_denominator_parse :
    SourceJson.intChars geometryRow3303_meanGapDenominatorChars = some (58615380000000 : Int) := by decide +kernel

theorem geometryRow3303_meanGap_denominator_nonzero : (58615380000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3303_meanGap_parse :
    parseRational geometryRow3303_meanGapText = .ok geometryRowsTyped3303.meanGap :=
  original_rational_fraction_of_chars geometryRow3303_meanGapNumeratorChars geometryRow3303_meanGapDenominatorChars
    (130592302061 : Int) (58615380000000 : Int)
    geometryRow3303_meanGap_numerator_no_slash geometryRow3303_meanGap_numerator_parse
    geometryRow3303_meanGap_denominator_parse geometryRow3303_meanGap_denominator_nonzero

theorem geometryRow3303_meanGap_read :
    rationalField geometryRowsJson3303 "mean_gap" = .ok geometryRowsTyped3303.meanGap :=
  original_rationalField_of_string geometryRowsJson3303 "mean_gap" geometryRow3303_meanGapText
    geometryRowsTyped3303.meanGap geometryRow3303_meanGap_field geometryRow3303_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_meanGap_complete"
  err.flush

noncomputable def geometryRow3303_jensenBoundNumeratorChars : List Char := ['1', '4', '9', '1', '0', '4', '0', '5', '9', '9', '8', '2', '3', '3', '8', '8', '8', '1', '0', '8', '4', '6', '8', '9', '3', '6', '5', '8', '0', '6', '9', '3', '9', '4', '0', '1', '0', '7', '5', '8', '3', '7', '8', '5', '3', '7', '2', '8', '5', '6', '3', '8', '3', '2', '6', '0', '5', '5', '1', '9', '6', '3', '3', '6', '5', '7', '8', '3', '6', '1', '4', '8', '1', '1', '0', '8', '2', '2', '2', '5', '9', '3', '3', '6', '8', '5', '1', '3', '1', '1', '5', '6', '4', '9', '6', '2', '1', '1', '2', '7', '5', '5', '8', '6', '2', '4', '8', '6', '4', '7', '7', '6', '6', '6', '9', '9', '0', '4', '5', '0', '6', '5', '4', '7', '9', '7', '1', '1', '2', '1', '3', '8', '9', '3', '9', '6', '8', '8', '8', '0', '9', '9', '6', '5', '7', '7', '3', '7', '6', '6', '5', '2', '1', '7', '1', '3', '0', '2', '5', '2', '9', '0', '8', '7', '1', '5', '5', '3', '9', '1', '5', '0', '8', '2', '2', '3', '6', '2', '3', '5', '3', '3', '2', '8', '6', '5', '1', '6', '4', '0', '6', '6', '9', '1', '0', '6', '1', '3', '1', '2', '8', '3', '8', '5', '1', '6', '9', '2', '3', '4', '7', '7', '6', '0', '8', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow3303_jensenBoundDenominatorChars : List Char := ['3', '3', '6', '8', '8', '4', '0', '0', '5', '9', '6', '2', '0', '7', '4', '4', '6', '2', '0', '6', '8', '1', '4', '9', '0', '9', '9', '7', '7', '5', '1', '3', '0', '6', '3', '6', '2', '3', '9', '5', '9', '6', '3', '5', '6', '8', '8', '3', '7', '1', '3', '0', '9', '2', '3', '7', '8', '7', '8', '3', '4', '4', '5', '9', '6', '1', '6', '8', '1', '3', '2', '0', '5', '4', '7', '8', '6', '4', '7', '1', '9', '9', '7', '2', '4', '4', '6', '0', '0', '6', '5', '4', '9', '0', '5', '3', '4', '7', '0', '5', '4', '0', '1', '0', '9', '2', '9', '6', '9', '5', '9', '4', '6', '6', '7', '5', '6', '1', '7', '9', '3', '3', '7', '0', '4', '2', '6', '2', '7', '9', '3', '9', '6', '3', '8', '0', '0', '2', '7', '0', '1', '7', '7', '3', '0', '2', '6', '7', '8', '9', '3', '4', '7', '9', '1', '9', '0', '4', '0', '5', '4', '9', '4', '6', '4', '6', '1', '6', '1', '0', '4', '7', '2', '1', '0', '3', '9', '3', '8', '7', '0', '4', '5', '3', '6', '3', '4', '1', '9', '4', '5', '2', '9', '3', '5', '4', '2', '7', '9', '5', '4', '3', '0', '1', '0', '3', '6', '3', '9', '4', '3', '7', '2', '4', '3', '1', '2', '8', '4', '7', '6', '7', '1', '5', '4', '3', '1', '5', '6', '0', '5', '5', '4', '5', '4', '3', '8', '2', '3', '3', '0', '5', '3', '3', '0', '8', '9', '8', '5', '5', '8', '8', '9']
noncomputable def geometryRow3303_jensenBoundText : String := String.ofList (geometryRow3303_jensenBoundNumeratorChars ++ '/' :: geometryRow3303_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_jensenBound_before_field"
  err.flush

theorem geometryRow3303_jensenBound_field :
    geometryRowsJson3303.getObjVal? "jensen_bound" = .ok (.str geometryRow3303_jensenBoundText) := by rfl

theorem geometryRow3303_jensenBound_numerator_no_slash :
    geometryRow3303_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow3303_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow3303_jensenBoundNumeratorChars = some (149104059982338881084689365806939401075837853728563832605519633657836148110822259336851311564962112755862486477666990450654797112138939688809965773766521713025290871553915082236235332865164066910613128385169234776085840000000000000000000000 : Int) := by decide +kernel

theorem geometryRow3303_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow3303_jensenBoundDenominatorChars = some (3368840059620744620681490997751306362395963568837130923787834459616813205478647199724460065490534705401092969594667561793370426279396380027017730267893479190405494646161047210393870453634194529354279543010363943724312847671543156055454382330533089855889 : Int) := by decide +kernel

theorem geometryRow3303_jensenBound_denominator_nonzero : (3368840059620744620681490997751306362395963568837130923787834459616813205478647199724460065490534705401092969594667561793370426279396380027017730267893479190405494646161047210393870453634194529354279543010363943724312847671543156055454382330533089855889 : Int) ≠ 0 := by decide +kernel

theorem geometryRow3303_jensenBound_parse :
    parseRational geometryRow3303_jensenBoundText = .ok geometryRowsTyped3303.jensenBound :=
  original_rational_fraction_of_chars geometryRow3303_jensenBoundNumeratorChars geometryRow3303_jensenBoundDenominatorChars
    (149104059982338881084689365806939401075837853728563832605519633657836148110822259336851311564962112755862486477666990450654797112138939688809965773766521713025290871553915082236235332865164066910613128385169234776085840000000000000000000000 : Int) (3368840059620744620681490997751306362395963568837130923787834459616813205478647199724460065490534705401092969594667561793370426279396380027017730267893479190405494646161047210393870453634194529354279543010363943724312847671543156055454382330533089855889 : Int)
    geometryRow3303_jensenBound_numerator_no_slash geometryRow3303_jensenBound_numerator_parse
    geometryRow3303_jensenBound_denominator_parse geometryRow3303_jensenBound_denominator_nonzero

theorem geometryRow3303_jensenBound_read :
    rationalField geometryRowsJson3303 "jensen_bound" = .ok geometryRowsTyped3303.jensenBound :=
  original_rationalField_of_string geometryRowsJson3303 "jensen_bound" geometryRow3303_jensenBoundText
    geometryRowsTyped3303.jensenBound geometryRow3303_jensenBound_field geometryRow3303_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_factorMaxima_before"
  err.flush

theorem geometryRow3303_factorMaxima_read :
    rationalArrayField geometryRowsJson3303 "factor_maxima" = .ok geometryRowsTyped3303.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_gapWeightedMeans_before"
  err.flush

theorem geometryRow3303_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson3303 "gap_weighted_means" = .ok geometryRowsTyped3303.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow3303_floorChars : List Char := ['3', '5', '0', '6', '6', '1', '9', '6', '3', '3', '6', '8', '6', '9', '9', '2']
noncomputable def geometryRow3303_floorText : String := String.ofList geometryRow3303_floorChars

theorem geometryRow3303_floor_text_read :
    geometryRowsJson3303.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow3303_floorText := by rfl

theorem geometryRow3303_floor_chars_parse :
    SourceJson.intChars geometryRow3303_floorChars = some (3506619633686992 : Int) := by decide +kernel

theorem geometryRow3303_floor_parse :
    parseInteger geometryRow3303_floorText = .ok geometryRowsTyped3303.jensenFloorQ96 := by
  simp only [geometryRow3303_floorText, parseInteger, String.toList_ofList, geometryRow3303_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_3303 :
    decodeGeometryRow geometryRowsJson3303 = .ok geometryRowsTyped3303 :=
  original_geometryRow_of_fields geometryRowsJson3303 geometryRowsTyped3303 geometryRow3303_floorText
    geometryRow3303_simplexId_read geometryRow3303_vertexIds_read
    geometryRow3303_physicalVolume_read geometryRow3303_meanGap_read
    geometryRow3303_factorMaxima_read geometryRow3303_gapWeightedMeans_read
    geometryRow3303_jensenBound_read geometryRow3303_floor_text_read geometryRow3303_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_3303_original_decoder_complete"
  err.flush

theorem geometryRow3303_shape :
    geometryRowsTyped3303.simplexId = 3303 ∧
    geometryRowsTyped3303.vertexIds.size = 9 ∧ geometryRowsTyped3303.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped3303.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped3303.factorMaxima.size = 10 ∧ geometryRowsTyped3303.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock412 : List SourceJson := [geometryRowsJson3296, geometryRowsJson3297, geometryRowsJson3298, geometryRowsJson3299, geometryRowsJson3300, geometryRowsJson3301, geometryRowsJson3302, geometryRowsJson3303]
noncomputable def geometryRowsTypedBlock412 : List GeometryRow := [geometryRowsTyped3296, geometryRowsTyped3297, geometryRowsTyped3298, geometryRowsTyped3299, geometryRowsTyped3300, geometryRowsTyped3301, geometryRowsTyped3302, geometryRowsTyped3303]

theorem geometry_Rows_block_412_push_eq (acc : List SourceJson) :
    SimplicesBlock412.blockPush acc = [geometryRowsJson3303, geometryRowsJson3302, geometryRowsJson3301, geometryRowsJson3300, geometryRowsJson3299, geometryRowsJson3298, geometryRowsJson3297, geometryRowsJson3296] ++ acc := by rfl

theorem geometry_Rows_block_412_reverse (acc : List SourceJson) :
    (SimplicesBlock412.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock412 := by
  rw [geometry_Rows_block_412_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_412 :
    geometryRowsJsonBlock412.mapM decodeGeometryRow = .ok geometryRowsTypedBlock412 := by
  simp only [geometryRowsJsonBlock412, geometryRowsTypedBlock412, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_3296, decode_geometry_Rows_3297, decode_geometry_Rows_3298, decode_geometry_Rows_3299, decode_geometry_Rows_3300, decode_geometry_Rows_3301, decode_geometry_Rows_3302, decode_geometry_Rows_3303]
  rfl

theorem geometry_Rows_block_412_length : geometryRowsTypedBlock412.length = 8 := by rfl

#print axioms geometryRow3296_simplexId_read
#print axioms geometryRow3296_vertexIds_read
#print axioms geometryRow3296_physicalVolume_field
#print axioms geometryRow3296_physicalVolume_numerator_no_slash
#print axioms geometryRow3296_physicalVolume_numerator_parse
#print axioms geometryRow3296_physicalVolume_denominator_parse
#print axioms geometryRow3296_physicalVolume_denominator_nonzero
#print axioms geometryRow3296_physicalVolume_parse
#print axioms geometryRow3296_physicalVolume_read
#print axioms geometryRow3296_meanGap_field
#print axioms geometryRow3296_meanGap_numerator_no_slash
#print axioms geometryRow3296_meanGap_numerator_parse
#print axioms geometryRow3296_meanGap_denominator_parse
#print axioms geometryRow3296_meanGap_denominator_nonzero
#print axioms geometryRow3296_meanGap_parse
#print axioms geometryRow3296_meanGap_read
#print axioms geometryRow3296_jensenBound_field
#print axioms geometryRow3296_jensenBound_numerator_no_slash
#print axioms geometryRow3296_jensenBound_numerator_parse
#print axioms geometryRow3296_jensenBound_denominator_parse
#print axioms geometryRow3296_jensenBound_denominator_nonzero
#print axioms geometryRow3296_jensenBound_parse
#print axioms geometryRow3296_jensenBound_read
#print axioms geometryRow3296_factorMaxima_read
#print axioms geometryRow3296_gapWeightedMeans_read
#print axioms geometryRow3296_floor_text_read
#print axioms geometryRow3296_floor_chars_parse
#print axioms geometryRow3296_floor_parse
#print axioms decode_geometry_Rows_3296
#print axioms geometryRow3296_shape
#print axioms geometryRow3297_simplexId_read
#print axioms geometryRow3297_vertexIds_read
#print axioms geometryRow3297_physicalVolume_field
#print axioms geometryRow3297_physicalVolume_numerator_no_slash
#print axioms geometryRow3297_physicalVolume_numerator_parse
#print axioms geometryRow3297_physicalVolume_denominator_parse
#print axioms geometryRow3297_physicalVolume_denominator_nonzero
#print axioms geometryRow3297_physicalVolume_parse
#print axioms geometryRow3297_physicalVolume_read
#print axioms geometryRow3297_meanGap_field
#print axioms geometryRow3297_meanGap_numerator_no_slash
#print axioms geometryRow3297_meanGap_numerator_parse
#print axioms geometryRow3297_meanGap_denominator_parse
#print axioms geometryRow3297_meanGap_denominator_nonzero
#print axioms geometryRow3297_meanGap_parse
#print axioms geometryRow3297_meanGap_read
#print axioms geometryRow3297_jensenBound_field
#print axioms geometryRow3297_jensenBound_numerator_no_slash
#print axioms geometryRow3297_jensenBound_numerator_parse
#print axioms geometryRow3297_jensenBound_denominator_parse
#print axioms geometryRow3297_jensenBound_denominator_nonzero
#print axioms geometryRow3297_jensenBound_parse
#print axioms geometryRow3297_jensenBound_read
#print axioms geometryRow3297_factorMaxima_read
#print axioms geometryRow3297_gapWeightedMeans_read
#print axioms geometryRow3297_floor_text_read
#print axioms geometryRow3297_floor_chars_parse
#print axioms geometryRow3297_floor_parse
#print axioms decode_geometry_Rows_3297
#print axioms geometryRow3297_shape
#print axioms geometryRow3298_simplexId_read
#print axioms geometryRow3298_vertexIds_read
#print axioms geometryRow3298_physicalVolume_field
#print axioms geometryRow3298_physicalVolume_numerator_no_slash
#print axioms geometryRow3298_physicalVolume_numerator_parse
#print axioms geometryRow3298_physicalVolume_denominator_parse
#print axioms geometryRow3298_physicalVolume_denominator_nonzero
#print axioms geometryRow3298_physicalVolume_parse
#print axioms geometryRow3298_physicalVolume_read
#print axioms geometryRow3298_meanGap_field
#print axioms geometryRow3298_meanGap_numerator_no_slash
#print axioms geometryRow3298_meanGap_numerator_parse
#print axioms geometryRow3298_meanGap_denominator_parse
#print axioms geometryRow3298_meanGap_denominator_nonzero
#print axioms geometryRow3298_meanGap_parse
#print axioms geometryRow3298_meanGap_read
#print axioms geometryRow3298_jensenBound_field
#print axioms geometryRow3298_jensenBound_numerator_no_slash
#print axioms geometryRow3298_jensenBound_numerator_parse
#print axioms geometryRow3298_jensenBound_denominator_parse
#print axioms geometryRow3298_jensenBound_denominator_nonzero
#print axioms geometryRow3298_jensenBound_parse
#print axioms geometryRow3298_jensenBound_read
#print axioms geometryRow3298_factorMaxima_read
#print axioms geometryRow3298_gapWeightedMeans_read
#print axioms geometryRow3298_floor_text_read
#print axioms geometryRow3298_floor_chars_parse
#print axioms geometryRow3298_floor_parse
#print axioms decode_geometry_Rows_3298
#print axioms geometryRow3298_shape
#print axioms geometryRow3299_simplexId_read
#print axioms geometryRow3299_vertexIds_read
#print axioms geometryRow3299_physicalVolume_field
#print axioms geometryRow3299_physicalVolume_numerator_no_slash
#print axioms geometryRow3299_physicalVolume_numerator_parse
#print axioms geometryRow3299_physicalVolume_denominator_parse
#print axioms geometryRow3299_physicalVolume_denominator_nonzero
#print axioms geometryRow3299_physicalVolume_parse
#print axioms geometryRow3299_physicalVolume_read
#print axioms geometryRow3299_meanGap_field
#print axioms geometryRow3299_meanGap_numerator_no_slash
#print axioms geometryRow3299_meanGap_numerator_parse
#print axioms geometryRow3299_meanGap_denominator_parse
#print axioms geometryRow3299_meanGap_denominator_nonzero
#print axioms geometryRow3299_meanGap_parse
#print axioms geometryRow3299_meanGap_read
#print axioms geometryRow3299_jensenBound_field
#print axioms geometryRow3299_jensenBound_numerator_no_slash
#print axioms geometryRow3299_jensenBound_numerator_parse
#print axioms geometryRow3299_jensenBound_denominator_parse
#print axioms geometryRow3299_jensenBound_denominator_nonzero
#print axioms geometryRow3299_jensenBound_parse
#print axioms geometryRow3299_jensenBound_read
#print axioms geometryRow3299_factorMaxima_read
#print axioms geometryRow3299_gapWeightedMeans_read
#print axioms geometryRow3299_floor_text_read
#print axioms geometryRow3299_floor_chars_parse
#print axioms geometryRow3299_floor_parse
#print axioms decode_geometry_Rows_3299
#print axioms geometryRow3299_shape
#print axioms geometryRow3300_simplexId_read
#print axioms geometryRow3300_vertexIds_read
#print axioms geometryRow3300_physicalVolume_field
#print axioms geometryRow3300_physicalVolume_numerator_no_slash
#print axioms geometryRow3300_physicalVolume_numerator_parse
#print axioms geometryRow3300_physicalVolume_denominator_parse
#print axioms geometryRow3300_physicalVolume_denominator_nonzero
#print axioms geometryRow3300_physicalVolume_parse
#print axioms geometryRow3300_physicalVolume_read
#print axioms geometryRow3300_meanGap_field
#print axioms geometryRow3300_meanGap_numerator_no_slash
#print axioms geometryRow3300_meanGap_numerator_parse
#print axioms geometryRow3300_meanGap_denominator_parse
#print axioms geometryRow3300_meanGap_denominator_nonzero
#print axioms geometryRow3300_meanGap_parse
#print axioms geometryRow3300_meanGap_read
#print axioms geometryRow3300_jensenBound_field
#print axioms geometryRow3300_jensenBound_numerator_no_slash
#print axioms geometryRow3300_jensenBound_numerator_parse
#print axioms geometryRow3300_jensenBound_denominator_parse
#print axioms geometryRow3300_jensenBound_denominator_nonzero
#print axioms geometryRow3300_jensenBound_parse
#print axioms geometryRow3300_jensenBound_read
#print axioms geometryRow3300_factorMaxima_read
#print axioms geometryRow3300_gapWeightedMeans_read
#print axioms geometryRow3300_floor_text_read
#print axioms geometryRow3300_floor_chars_parse
#print axioms geometryRow3300_floor_parse
#print axioms decode_geometry_Rows_3300
#print axioms geometryRow3300_shape
#print axioms geometryRow3301_simplexId_read
#print axioms geometryRow3301_vertexIds_read
#print axioms geometryRow3301_physicalVolume_field
#print axioms geometryRow3301_physicalVolume_numerator_no_slash
#print axioms geometryRow3301_physicalVolume_numerator_parse
#print axioms geometryRow3301_physicalVolume_denominator_parse
#print axioms geometryRow3301_physicalVolume_denominator_nonzero
#print axioms geometryRow3301_physicalVolume_parse
#print axioms geometryRow3301_physicalVolume_read
#print axioms geometryRow3301_meanGap_field
#print axioms geometryRow3301_meanGap_numerator_no_slash
#print axioms geometryRow3301_meanGap_numerator_parse
#print axioms geometryRow3301_meanGap_denominator_parse
#print axioms geometryRow3301_meanGap_denominator_nonzero
#print axioms geometryRow3301_meanGap_parse
#print axioms geometryRow3301_meanGap_read
#print axioms geometryRow3301_jensenBound_field
#print axioms geometryRow3301_jensenBound_numerator_no_slash
#print axioms geometryRow3301_jensenBound_numerator_parse
#print axioms geometryRow3301_jensenBound_denominator_parse
#print axioms geometryRow3301_jensenBound_denominator_nonzero
#print axioms geometryRow3301_jensenBound_parse
#print axioms geometryRow3301_jensenBound_read
#print axioms geometryRow3301_factorMaxima_read
#print axioms geometryRow3301_gapWeightedMeans_read
#print axioms geometryRow3301_floor_text_read
#print axioms geometryRow3301_floor_chars_parse
#print axioms geometryRow3301_floor_parse
#print axioms decode_geometry_Rows_3301
#print axioms geometryRow3301_shape
#print axioms geometryRow3302_simplexId_read
#print axioms geometryRow3302_vertexIds_read
#print axioms geometryRow3302_physicalVolume_field
#print axioms geometryRow3302_physicalVolume_numerator_no_slash
#print axioms geometryRow3302_physicalVolume_numerator_parse
#print axioms geometryRow3302_physicalVolume_denominator_parse
#print axioms geometryRow3302_physicalVolume_denominator_nonzero
#print axioms geometryRow3302_physicalVolume_parse
#print axioms geometryRow3302_physicalVolume_read
#print axioms geometryRow3302_meanGap_field
#print axioms geometryRow3302_meanGap_numerator_no_slash
#print axioms geometryRow3302_meanGap_numerator_parse
#print axioms geometryRow3302_meanGap_denominator_parse
#print axioms geometryRow3302_meanGap_denominator_nonzero
#print axioms geometryRow3302_meanGap_parse
#print axioms geometryRow3302_meanGap_read
#print axioms geometryRow3302_jensenBound_field
#print axioms geometryRow3302_jensenBound_numerator_no_slash
#print axioms geometryRow3302_jensenBound_numerator_parse
#print axioms geometryRow3302_jensenBound_denominator_parse
#print axioms geometryRow3302_jensenBound_denominator_nonzero
#print axioms geometryRow3302_jensenBound_parse
#print axioms geometryRow3302_jensenBound_read
#print axioms geometryRow3302_factorMaxima_read
#print axioms geometryRow3302_gapWeightedMeans_read
#print axioms geometryRow3302_floor_text_read
#print axioms geometryRow3302_floor_chars_parse
#print axioms geometryRow3302_floor_parse
#print axioms decode_geometry_Rows_3302
#print axioms geometryRow3302_shape
#print axioms geometryRow3303_simplexId_read
#print axioms geometryRow3303_vertexIds_read
#print axioms geometryRow3303_physicalVolume_field
#print axioms geometryRow3303_physicalVolume_numerator_no_slash
#print axioms geometryRow3303_physicalVolume_numerator_parse
#print axioms geometryRow3303_physicalVolume_denominator_parse
#print axioms geometryRow3303_physicalVolume_denominator_nonzero
#print axioms geometryRow3303_physicalVolume_parse
#print axioms geometryRow3303_physicalVolume_read
#print axioms geometryRow3303_meanGap_field
#print axioms geometryRow3303_meanGap_numerator_no_slash
#print axioms geometryRow3303_meanGap_numerator_parse
#print axioms geometryRow3303_meanGap_denominator_parse
#print axioms geometryRow3303_meanGap_denominator_nonzero
#print axioms geometryRow3303_meanGap_parse
#print axioms geometryRow3303_meanGap_read
#print axioms geometryRow3303_jensenBound_field
#print axioms geometryRow3303_jensenBound_numerator_no_slash
#print axioms geometryRow3303_jensenBound_numerator_parse
#print axioms geometryRow3303_jensenBound_denominator_parse
#print axioms geometryRow3303_jensenBound_denominator_nonzero
#print axioms geometryRow3303_jensenBound_parse
#print axioms geometryRow3303_jensenBound_read
#print axioms geometryRow3303_factorMaxima_read
#print axioms geometryRow3303_gapWeightedMeans_read
#print axioms geometryRow3303_floor_text_read
#print axioms geometryRow3303_floor_chars_parse
#print axioms geometryRow3303_floor_parse
#print axioms decode_geometry_Rows_3303
#print axioms geometryRow3303_shape
#print axioms geometry_Rows_block_412_push_eq
#print axioms geometry_Rows_block_412_reverse
#print axioms decode_geometry_Rows_block_412
#print axioms geometry_Rows_block_412_length

end ImbalancedChen.P2OriginalSaving19Geometry12ScalableDecoding
