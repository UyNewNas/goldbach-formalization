import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableSimplicesBlock005

/-! Local typed certificates for original cell 05, rows 40 through 47.
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

noncomputable def geometryRowsJson040 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped040 : GeometryRow :=
  { simplexId := 40,
    vertexIds := #[27, 25, 23, 22, 20, 18, 6, 4, 0],
    physicalVolume := ((17426206191717883934813684091631890127 : ℚ) / (202208681914804687500000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2531241 : ℚ) / (26500000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((1934699989504957 : ℚ) / (22082428800000000 : ℚ)), ((243252193099889 : ℚ) / (2760303600000000 : ℚ)), ((1901992631986501 : ℚ) / (15457700160000000 : ℚ)), ((3632668003504633 : ℚ) / (38644250400000000 : ℚ)), ((3469168280795387 : ℚ) / (38644250400000000 : ℚ)), ((546257804798161 : ℚ) / (7728850080000000 : ℚ)), ((2886352808378311 : ℚ) / (77288500800000000 : ℚ)), ((119392648603799 : ℚ) / (3680404800000000 : ℚ)), ((39131019335453 : ℚ) / (1226801600000000 : ℚ)), ((9222240543587 : ℚ) / (306700400000000 : ℚ))],
    jensenBound := ((114242762958788222457328343885382966959649143918322057260817165696815500183089159153871280116976369319364106649600000000000000000000000 : ℚ) / (766324240456849652456353633996834735156477711281908495999362603667071814966320413803183514280298973284555359976443192245651530074397970393259393877 : ℚ)),
    jensenFloorQ96 := (11811246091317022 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_simplexId_before"
  err.flush

theorem geometryRow040_simplexId_read :
    geometryRowsJson040.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped040.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_vertexIds_before"
  err.flush

theorem geometryRow040_vertexIds_read :
    geometryRowsJson040.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped040.vertexIds := by decide +kernel

noncomputable def geometryRow040_physicalVolumeNumeratorChars : List Char := ['1', '7', '4', '2', '6', '2', '0', '6', '1', '9', '1', '7', '1', '7', '8', '8', '3', '9', '3', '4', '8', '1', '3', '6', '8', '4', '0', '9', '1', '6', '3', '1', '8', '9', '0', '1', '2', '7']
noncomputable def geometryRow040_physicalVolumeDenominatorChars : List Char := ['2', '0', '2', '2', '0', '8', '6', '8', '1', '9', '1', '4', '8', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow040_physicalVolumeText : String := String.ofList (geometryRow040_physicalVolumeNumeratorChars ++ '/' :: geometryRow040_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_physicalVolume_before_field"
  err.flush

theorem geometryRow040_physicalVolume_field :
    geometryRowsJson040.getObjVal? "physical_volume" = .ok (.str geometryRow040_physicalVolumeText) := by rfl

theorem geometryRow040_physicalVolume_numerator_no_slash :
    geometryRow040_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow040_physicalVolumeNumeratorChars = some (17426206191717883934813684091631890127 : Int) := by decide +kernel

theorem geometryRow040_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow040_physicalVolumeDenominatorChars = some (202208681914804687500000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow040_physicalVolume_denominator_nonzero : (202208681914804687500000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_physicalVolume_parse :
    parseRational geometryRow040_physicalVolumeText = .ok geometryRowsTyped040.physicalVolume :=
  original_rational_fraction_of_chars geometryRow040_physicalVolumeNumeratorChars geometryRow040_physicalVolumeDenominatorChars
    (17426206191717883934813684091631890127 : Int) (202208681914804687500000000000000000000000000000000000000000 : Int)
    geometryRow040_physicalVolume_numerator_no_slash geometryRow040_physicalVolume_numerator_parse
    geometryRow040_physicalVolume_denominator_parse geometryRow040_physicalVolume_denominator_nonzero

theorem geometryRow040_physicalVolume_read :
    rationalField geometryRowsJson040 "physical_volume" = .ok geometryRowsTyped040.physicalVolume :=
  original_rationalField_of_string geometryRowsJson040 "physical_volume" geometryRow040_physicalVolumeText
    geometryRowsTyped040.physicalVolume geometryRow040_physicalVolume_field geometryRow040_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_physicalVolume_complete"
  err.flush

noncomputable def geometryRow040_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow040_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow040_meanGapText : String := String.ofList (geometryRow040_meanGapNumeratorChars ++ '/' :: geometryRow040_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_meanGap_before_field"
  err.flush

theorem geometryRow040_meanGap_field :
    geometryRowsJson040.getObjVal? "mean_gap" = .ok (.str geometryRow040_meanGapText) := by rfl

theorem geometryRow040_meanGap_numerator_no_slash :
    geometryRow040_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_meanGap_numerator_parse :
    SourceJson.intChars geometryRow040_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow040_meanGap_denominator_parse :
    SourceJson.intChars geometryRow040_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow040_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_meanGap_parse :
    parseRational geometryRow040_meanGapText = .ok geometryRowsTyped040.meanGap :=
  original_rational_fraction_of_chars geometryRow040_meanGapNumeratorChars geometryRow040_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow040_meanGap_numerator_no_slash geometryRow040_meanGap_numerator_parse
    geometryRow040_meanGap_denominator_parse geometryRow040_meanGap_denominator_nonzero

theorem geometryRow040_meanGap_read :
    rationalField geometryRowsJson040 "mean_gap" = .ok geometryRowsTyped040.meanGap :=
  original_rationalField_of_string geometryRowsJson040 "mean_gap" geometryRow040_meanGapText
    geometryRowsTyped040.meanGap geometryRow040_meanGap_field geometryRow040_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_meanGap_complete"
  err.flush

noncomputable def geometryRow040_jensenBoundNumeratorChars : List Char := ['1', '1', '4', '2', '4', '2', '7', '6', '2', '9', '5', '8', '7', '8', '8', '2', '2', '2', '4', '5', '7', '3', '2', '8', '3', '4', '3', '8', '8', '5', '3', '8', '2', '9', '6', '6', '9', '5', '9', '6', '4', '9', '1', '4', '3', '9', '1', '8', '3', '2', '2', '0', '5', '7', '2', '6', '0', '8', '1', '7', '1', '6', '5', '6', '9', '6', '8', '1', '5', '5', '0', '0', '1', '8', '3', '0', '8', '9', '1', '5', '9', '1', '5', '3', '8', '7', '1', '2', '8', '0', '1', '1', '6', '9', '7', '6', '3', '6', '9', '3', '1', '9', '3', '6', '4', '1', '0', '6', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow040_jensenBoundDenominatorChars : List Char := ['7', '6', '6', '3', '2', '4', '2', '4', '0', '4', '5', '6', '8', '4', '9', '6', '5', '2', '4', '5', '6', '3', '5', '3', '6', '3', '3', '9', '9', '6', '8', '3', '4', '7', '3', '5', '1', '5', '6', '4', '7', '7', '7', '1', '1', '2', '8', '1', '9', '0', '8', '4', '9', '5', '9', '9', '9', '3', '6', '2', '6', '0', '3', '6', '6', '7', '0', '7', '1', '8', '1', '4', '9', '6', '6', '3', '2', '0', '4', '1', '3', '8', '0', '3', '1', '8', '3', '5', '1', '4', '2', '8', '0', '2', '9', '8', '9', '7', '3', '2', '8', '4', '5', '5', '5', '3', '5', '9', '9', '7', '6', '4', '4', '3', '1', '9', '2', '2', '4', '5', '6', '5', '1', '5', '3', '0', '0', '7', '4', '3', '9', '7', '9', '7', '0', '3', '9', '3', '2', '5', '9', '3', '9', '3', '8', '7', '7']
noncomputable def geometryRow040_jensenBoundText : String := String.ofList (geometryRow040_jensenBoundNumeratorChars ++ '/' :: geometryRow040_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_jensenBound_before_field"
  err.flush

theorem geometryRow040_jensenBound_field :
    geometryRowsJson040.getObjVal? "jensen_bound" = .ok (.str geometryRow040_jensenBoundText) := by rfl

theorem geometryRow040_jensenBound_numerator_no_slash :
    geometryRow040_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow040_jensenBoundNumeratorChars = some (114242762958788222457328343885382966959649143918322057260817165696815500183089159153871280116976369319364106649600000000000000000000000 : Int) := by decide +kernel

theorem geometryRow040_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow040_jensenBoundDenominatorChars = some (766324240456849652456353633996834735156477711281908495999362603667071814966320413803183514280298973284555359976443192245651530074397970393259393877 : Int) := by decide +kernel

theorem geometryRow040_jensenBound_denominator_nonzero : (766324240456849652456353633996834735156477711281908495999362603667071814966320413803183514280298973284555359976443192245651530074397970393259393877 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_jensenBound_parse :
    parseRational geometryRow040_jensenBoundText = .ok geometryRowsTyped040.jensenBound :=
  original_rational_fraction_of_chars geometryRow040_jensenBoundNumeratorChars geometryRow040_jensenBoundDenominatorChars
    (114242762958788222457328343885382966959649143918322057260817165696815500183089159153871280116976369319364106649600000000000000000000000 : Int) (766324240456849652456353633996834735156477711281908495999362603667071814966320413803183514280298973284555359976443192245651530074397970393259393877 : Int)
    geometryRow040_jensenBound_numerator_no_slash geometryRow040_jensenBound_numerator_parse
    geometryRow040_jensenBound_denominator_parse geometryRow040_jensenBound_denominator_nonzero

theorem geometryRow040_jensenBound_read :
    rationalField geometryRowsJson040 "jensen_bound" = .ok geometryRowsTyped040.jensenBound :=
  original_rationalField_of_string geometryRowsJson040 "jensen_bound" geometryRow040_jensenBoundText
    geometryRowsTyped040.jensenBound geometryRow040_jensenBound_field geometryRow040_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_factorMaxima_before"
  err.flush

theorem geometryRow040_factorMaxima_read :
    rationalArrayField geometryRowsJson040 "factor_maxima" = .ok geometryRowsTyped040.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_gapWeightedMeans_before"
  err.flush

theorem geometryRow040_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson040 "gap_weighted_means" = .ok geometryRowsTyped040.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow040_floorChars : List Char := ['1', '1', '8', '1', '1', '2', '4', '6', '0', '9', '1', '3', '1', '7', '0', '2', '2']
noncomputable def geometryRow040_floorText : String := String.ofList geometryRow040_floorChars

theorem geometryRow040_floor_text_read :
    geometryRowsJson040.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow040_floorText := by rfl

theorem geometryRow040_floor_chars_parse :
    SourceJson.intChars geometryRow040_floorChars = some (11811246091317022 : Int) := by decide +kernel

theorem geometryRow040_floor_parse :
    parseInteger geometryRow040_floorText = .ok geometryRowsTyped040.jensenFloorQ96 := by
  simp only [geometryRow040_floorText, parseInteger, String.toList_ofList, geometryRow040_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_040 :
    decodeGeometryRow geometryRowsJson040 = .ok geometryRowsTyped040 :=
  original_geometryRow_of_fields geometryRowsJson040 geometryRowsTyped040 geometryRow040_floorText
    geometryRow040_simplexId_read geometryRow040_vertexIds_read
    geometryRow040_physicalVolume_read geometryRow040_meanGap_read
    geometryRow040_factorMaxima_read geometryRow040_gapWeightedMeans_read
    geometryRow040_jensenBound_read geometryRow040_floor_text_read geometryRow040_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_040_original_decoder_complete"
  err.flush

theorem geometryRow040_shape :
    geometryRowsTyped040.simplexId = 40 ∧
    geometryRowsTyped040.vertexIds.size = 9 ∧ geometryRowsTyped040.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped040.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped040.factorMaxima.size = 10 ∧ geometryRowsTyped040.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson041 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped041 : GeometryRow :=
  { simplexId := 41,
    vertexIds := #[27, 25, 23, 22, 20, 18, 16, 4, 0],
    physicalVolume := ((5149184979665930440494978507673183 : ℚ) / (66237120648193359375000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2409379 : ℚ) / (25600000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((35941909805849 : ℚ) / (416649600000000 : ℚ)), ((4519431073123 : ℚ) / (52081200000000 : ℚ)), ((36144582412529 : ℚ) / (291654720000000 : ℚ)), ((69513481929161 : ℚ) / (729136800000000 : ℚ)), ((66729416007139 : ℚ) / (729136800000000 : ℚ)), ((2044582344097 : ℚ) / (29165472000000 : ℚ)), ((54878270340227 : ℚ) / (1458273600000000 : ℚ)), ((2192825934323 : ℚ) / (69441600000000 : ℚ)), ((2155097809843 : ℚ) / (69441600000000 : ℚ)), ((514209954827 : ℚ) / (17360400000000 : ℚ))],
    jensenBound := ((3324955385896063603366421982335645035710735573395222825120634259249405263050973488566297952256000000000000000000000 : ℚ) / (23277720981595076329005494508876467347520775805619189321169831912677429589176994191656754187723240497352609318495626841026646271 : ℚ)),
    jensenFloorQ96 := (11316834060977760 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_simplexId_before"
  err.flush

theorem geometryRow041_simplexId_read :
    geometryRowsJson041.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped041.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_vertexIds_before"
  err.flush

theorem geometryRow041_vertexIds_read :
    geometryRowsJson041.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped041.vertexIds := by decide +kernel

noncomputable def geometryRow041_physicalVolumeNumeratorChars : List Char := ['5', '1', '4', '9', '1', '8', '4', '9', '7', '9', '6', '6', '5', '9', '3', '0', '4', '4', '0', '4', '9', '4', '9', '7', '8', '5', '0', '7', '6', '7', '3', '1', '8', '3']
noncomputable def geometryRow041_physicalVolumeDenominatorChars : List Char := ['6', '6', '2', '3', '7', '1', '2', '0', '6', '4', '8', '1', '9', '3', '3', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_physicalVolumeText : String := String.ofList (geometryRow041_physicalVolumeNumeratorChars ++ '/' :: geometryRow041_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_physicalVolume_before_field"
  err.flush

theorem geometryRow041_physicalVolume_field :
    geometryRowsJson041.getObjVal? "physical_volume" = .ok (.str geometryRow041_physicalVolumeText) := by rfl

theorem geometryRow041_physicalVolume_numerator_no_slash :
    geometryRow041_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow041_physicalVolumeNumeratorChars = some (5149184979665930440494978507673183 : Int) := by decide +kernel

theorem geometryRow041_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow041_physicalVolumeDenominatorChars = some (66237120648193359375000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow041_physicalVolume_denominator_nonzero : (66237120648193359375000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_physicalVolume_parse :
    parseRational geometryRow041_physicalVolumeText = .ok geometryRowsTyped041.physicalVolume :=
  original_rational_fraction_of_chars geometryRow041_physicalVolumeNumeratorChars geometryRow041_physicalVolumeDenominatorChars
    (5149184979665930440494978507673183 : Int) (66237120648193359375000000000000000000000000000000000000 : Int)
    geometryRow041_physicalVolume_numerator_no_slash geometryRow041_physicalVolume_numerator_parse
    geometryRow041_physicalVolume_denominator_parse geometryRow041_physicalVolume_denominator_nonzero

theorem geometryRow041_physicalVolume_read :
    rationalField geometryRowsJson041 "physical_volume" = .ok geometryRowsTyped041.physicalVolume :=
  original_rationalField_of_string geometryRowsJson041 "physical_volume" geometryRow041_physicalVolumeText
    geometryRowsTyped041.physicalVolume geometryRow041_physicalVolume_field geometryRow041_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_physicalVolume_complete"
  err.flush

noncomputable def geometryRow041_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow041_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_meanGapText : String := String.ofList (geometryRow041_meanGapNumeratorChars ++ '/' :: geometryRow041_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_meanGap_before_field"
  err.flush

theorem geometryRow041_meanGap_field :
    geometryRowsJson041.getObjVal? "mean_gap" = .ok (.str geometryRow041_meanGapText) := by rfl

theorem geometryRow041_meanGap_numerator_no_slash :
    geometryRow041_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_meanGap_numerator_parse :
    SourceJson.intChars geometryRow041_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow041_meanGap_denominator_parse :
    SourceJson.intChars geometryRow041_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow041_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_meanGap_parse :
    parseRational geometryRow041_meanGapText = .ok geometryRowsTyped041.meanGap :=
  original_rational_fraction_of_chars geometryRow041_meanGapNumeratorChars geometryRow041_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow041_meanGap_numerator_no_slash geometryRow041_meanGap_numerator_parse
    geometryRow041_meanGap_denominator_parse geometryRow041_meanGap_denominator_nonzero

theorem geometryRow041_meanGap_read :
    rationalField geometryRowsJson041 "mean_gap" = .ok geometryRowsTyped041.meanGap :=
  original_rationalField_of_string geometryRowsJson041 "mean_gap" geometryRow041_meanGapText
    geometryRowsTyped041.meanGap geometryRow041_meanGap_field geometryRow041_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_meanGap_complete"
  err.flush

noncomputable def geometryRow041_jensenBoundNumeratorChars : List Char := ['3', '3', '2', '4', '9', '5', '5', '3', '8', '5', '8', '9', '6', '0', '6', '3', '6', '0', '3', '3', '6', '6', '4', '2', '1', '9', '8', '2', '3', '3', '5', '6', '4', '5', '0', '3', '5', '7', '1', '0', '7', '3', '5', '5', '7', '3', '3', '9', '5', '2', '2', '2', '8', '2', '5', '1', '2', '0', '6', '3', '4', '2', '5', '9', '2', '4', '9', '4', '0', '5', '2', '6', '3', '0', '5', '0', '9', '7', '3', '4', '8', '8', '5', '6', '6', '2', '9', '7', '9', '5', '2', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_jensenBoundDenominatorChars : List Char := ['2', '3', '2', '7', '7', '7', '2', '0', '9', '8', '1', '5', '9', '5', '0', '7', '6', '3', '2', '9', '0', '0', '5', '4', '9', '4', '5', '0', '8', '8', '7', '6', '4', '6', '7', '3', '4', '7', '5', '2', '0', '7', '7', '5', '8', '0', '5', '6', '1', '9', '1', '8', '9', '3', '2', '1', '1', '6', '9', '8', '3', '1', '9', '1', '2', '6', '7', '7', '4', '2', '9', '5', '8', '9', '1', '7', '6', '9', '9', '4', '1', '9', '1', '6', '5', '6', '7', '5', '4', '1', '8', '7', '7', '2', '3', '2', '4', '0', '4', '9', '7', '3', '5', '2', '6', '0', '9', '3', '1', '8', '4', '9', '5', '6', '2', '6', '8', '4', '1', '0', '2', '6', '6', '4', '6', '2', '7', '1']
noncomputable def geometryRow041_jensenBoundText : String := String.ofList (geometryRow041_jensenBoundNumeratorChars ++ '/' :: geometryRow041_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_jensenBound_before_field"
  err.flush

theorem geometryRow041_jensenBound_field :
    geometryRowsJson041.getObjVal? "jensen_bound" = .ok (.str geometryRow041_jensenBoundText) := by rfl

theorem geometryRow041_jensenBound_numerator_no_slash :
    geometryRow041_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow041_jensenBoundNumeratorChars = some (3324955385896063603366421982335645035710735573395222825120634259249405263050973488566297952256000000000000000000000 : Int) := by decide +kernel

theorem geometryRow041_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow041_jensenBoundDenominatorChars = some (23277720981595076329005494508876467347520775805619189321169831912677429589176994191656754187723240497352609318495626841026646271 : Int) := by decide +kernel

theorem geometryRow041_jensenBound_denominator_nonzero : (23277720981595076329005494508876467347520775805619189321169831912677429589176994191656754187723240497352609318495626841026646271 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_jensenBound_parse :
    parseRational geometryRow041_jensenBoundText = .ok geometryRowsTyped041.jensenBound :=
  original_rational_fraction_of_chars geometryRow041_jensenBoundNumeratorChars geometryRow041_jensenBoundDenominatorChars
    (3324955385896063603366421982335645035710735573395222825120634259249405263050973488566297952256000000000000000000000 : Int) (23277720981595076329005494508876467347520775805619189321169831912677429589176994191656754187723240497352609318495626841026646271 : Int)
    geometryRow041_jensenBound_numerator_no_slash geometryRow041_jensenBound_numerator_parse
    geometryRow041_jensenBound_denominator_parse geometryRow041_jensenBound_denominator_nonzero

theorem geometryRow041_jensenBound_read :
    rationalField geometryRowsJson041 "jensen_bound" = .ok geometryRowsTyped041.jensenBound :=
  original_rationalField_of_string geometryRowsJson041 "jensen_bound" geometryRow041_jensenBoundText
    geometryRowsTyped041.jensenBound geometryRow041_jensenBound_field geometryRow041_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_factorMaxima_before"
  err.flush

theorem geometryRow041_factorMaxima_read :
    rationalArrayField geometryRowsJson041 "factor_maxima" = .ok geometryRowsTyped041.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_gapWeightedMeans_before"
  err.flush

theorem geometryRow041_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson041 "gap_weighted_means" = .ok geometryRowsTyped041.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow041_floorChars : List Char := ['1', '1', '3', '1', '6', '8', '3', '4', '0', '6', '0', '9', '7', '7', '7', '6', '0']
noncomputable def geometryRow041_floorText : String := String.ofList geometryRow041_floorChars

theorem geometryRow041_floor_text_read :
    geometryRowsJson041.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow041_floorText := by rfl

theorem geometryRow041_floor_chars_parse :
    SourceJson.intChars geometryRow041_floorChars = some (11316834060977760 : Int) := by decide +kernel

theorem geometryRow041_floor_parse :
    parseInteger geometryRow041_floorText = .ok geometryRowsTyped041.jensenFloorQ96 := by
  simp only [geometryRow041_floorText, parseInteger, String.toList_ofList, geometryRow041_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_041 :
    decodeGeometryRow geometryRowsJson041 = .ok geometryRowsTyped041 :=
  original_geometryRow_of_fields geometryRowsJson041 geometryRowsTyped041 geometryRow041_floorText
    geometryRow041_simplexId_read geometryRow041_vertexIds_read
    geometryRow041_physicalVolume_read geometryRow041_meanGap_read
    geometryRow041_factorMaxima_read geometryRow041_gapWeightedMeans_read
    geometryRow041_jensenBound_read geometryRow041_floor_text_read geometryRow041_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_041_original_decoder_complete"
  err.flush

theorem geometryRow041_shape :
    geometryRowsTyped041.simplexId = 41 ∧
    geometryRowsTyped041.vertexIds.size = 9 ∧ geometryRowsTyped041.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped041.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped041.factorMaxima.size = 10 ∧ geometryRowsTyped041.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson042 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped042 : GeometryRow :=
  { simplexId := 42,
    vertexIds := #[27, 25, 23, 22, 20, 18, 16, 14, 4],
    physicalVolume := ((3270981331912044738562074158660293 : ℚ) / (75403865023612976074218750000000000000000000000000000000 : ℚ)),
    meanGap := ((51871037 : ℚ) / (97920000000 : ℚ)),
    factorMaxima := #[((2409379 : ℚ) / (25600000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2390621 : ℚ) / (32000000 : ℚ)), ((515597 : ℚ) / (12000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((12873980053166896064707 : ℚ) / (151284327723446400000000 : ℚ)), ((95458613657102652499 : ℚ) / (1112384762672400000000 : ℚ)), ((9477927328032724006553 : ℚ) / (75642163861723200000000 : ℚ)), ((526445246552904876259 : ℚ) / (5403011704408800000000 : ℚ)), ((502876233364104571553 : ℚ) / (5403011704408800000000 : ℚ)), ((516823179252165225157 : ℚ) / (7564216386172320000000 : ℚ)), ((2726071046850005069287 : ℚ) / (75642163861723200000000 : ℚ)), ((791550158208613173401 : ℚ) / (25214054620574400000000 : ℚ)), ((259283726540904791027 : ℚ) / (8404684873524800000000 : ℚ)), ((3621301576501378857 : ℚ) / (123598306963600000000 : ℚ))],
    jensenBound := ((170634162783436087262404841015991523640018248987029120200313645525482170075473407116370469488881526463319646511219456479664607649524507077119754423901816423412233913034080256000000000000000000000 : ℚ) / (1076296532339399778687938540981942659424200360459848834842410409436772898005356793967860084983412812090966741101837998835404513390313583968256459913333735155000992343605717024985436852078628816965223687929961 : ℚ)),
    jensenFloorQ96 := (12560693798861384 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_simplexId_before"
  err.flush

theorem geometryRow042_simplexId_read :
    geometryRowsJson042.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped042.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_vertexIds_before"
  err.flush

theorem geometryRow042_vertexIds_read :
    geometryRowsJson042.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped042.vertexIds := by decide +kernel

noncomputable def geometryRow042_physicalVolumeNumeratorChars : List Char := ['3', '2', '7', '0', '9', '8', '1', '3', '3', '1', '9', '1', '2', '0', '4', '4', '7', '3', '8', '5', '6', '2', '0', '7', '4', '1', '5', '8', '6', '6', '0', '2', '9', '3']
noncomputable def geometryRow042_physicalVolumeDenominatorChars : List Char := ['7', '5', '4', '0', '3', '8', '6', '5', '0', '2', '3', '6', '1', '2', '9', '7', '6', '0', '7', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow042_physicalVolumeText : String := String.ofList (geometryRow042_physicalVolumeNumeratorChars ++ '/' :: geometryRow042_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_physicalVolume_before_field"
  err.flush

theorem geometryRow042_physicalVolume_field :
    geometryRowsJson042.getObjVal? "physical_volume" = .ok (.str geometryRow042_physicalVolumeText) := by rfl

theorem geometryRow042_physicalVolume_numerator_no_slash :
    geometryRow042_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow042_physicalVolumeNumeratorChars = some (3270981331912044738562074158660293 : Int) := by decide +kernel

theorem geometryRow042_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow042_physicalVolumeDenominatorChars = some (75403865023612976074218750000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow042_physicalVolume_denominator_nonzero : (75403865023612976074218750000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_physicalVolume_parse :
    parseRational geometryRow042_physicalVolumeText = .ok geometryRowsTyped042.physicalVolume :=
  original_rational_fraction_of_chars geometryRow042_physicalVolumeNumeratorChars geometryRow042_physicalVolumeDenominatorChars
    (3270981331912044738562074158660293 : Int) (75403865023612976074218750000000000000000000000000000000 : Int)
    geometryRow042_physicalVolume_numerator_no_slash geometryRow042_physicalVolume_numerator_parse
    geometryRow042_physicalVolume_denominator_parse geometryRow042_physicalVolume_denominator_nonzero

theorem geometryRow042_physicalVolume_read :
    rationalField geometryRowsJson042 "physical_volume" = .ok geometryRowsTyped042.physicalVolume :=
  original_rationalField_of_string geometryRowsJson042 "physical_volume" geometryRow042_physicalVolumeText
    geometryRowsTyped042.physicalVolume geometryRow042_physicalVolume_field geometryRow042_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_physicalVolume_complete"
  err.flush

noncomputable def geometryRow042_meanGapNumeratorChars : List Char := ['5', '1', '8', '7', '1', '0', '3', '7']
noncomputable def geometryRow042_meanGapDenominatorChars : List Char := ['9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow042_meanGapText : String := String.ofList (geometryRow042_meanGapNumeratorChars ++ '/' :: geometryRow042_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_meanGap_before_field"
  err.flush

theorem geometryRow042_meanGap_field :
    geometryRowsJson042.getObjVal? "mean_gap" = .ok (.str geometryRow042_meanGapText) := by rfl

theorem geometryRow042_meanGap_numerator_no_slash :
    geometryRow042_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_meanGap_numerator_parse :
    SourceJson.intChars geometryRow042_meanGapNumeratorChars = some (51871037 : Int) := by decide +kernel

theorem geometryRow042_meanGap_denominator_parse :
    SourceJson.intChars geometryRow042_meanGapDenominatorChars = some (97920000000 : Int) := by decide +kernel

theorem geometryRow042_meanGap_denominator_nonzero : (97920000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_meanGap_parse :
    parseRational geometryRow042_meanGapText = .ok geometryRowsTyped042.meanGap :=
  original_rational_fraction_of_chars geometryRow042_meanGapNumeratorChars geometryRow042_meanGapDenominatorChars
    (51871037 : Int) (97920000000 : Int)
    geometryRow042_meanGap_numerator_no_slash geometryRow042_meanGap_numerator_parse
    geometryRow042_meanGap_denominator_parse geometryRow042_meanGap_denominator_nonzero

theorem geometryRow042_meanGap_read :
    rationalField geometryRowsJson042 "mean_gap" = .ok geometryRowsTyped042.meanGap :=
  original_rationalField_of_string geometryRowsJson042 "mean_gap" geometryRow042_meanGapText
    geometryRowsTyped042.meanGap geometryRow042_meanGap_field geometryRow042_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_meanGap_complete"
  err.flush

noncomputable def geometryRow042_jensenBoundNumeratorChars : List Char := ['1', '7', '0', '6', '3', '4', '1', '6', '2', '7', '8', '3', '4', '3', '6', '0', '8', '7', '2', '6', '2', '4', '0', '4', '8', '4', '1', '0', '1', '5', '9', '9', '1', '5', '2', '3', '6', '4', '0', '0', '1', '8', '2', '4', '8', '9', '8', '7', '0', '2', '9', '1', '2', '0', '2', '0', '0', '3', '1', '3', '6', '4', '5', '5', '2', '5', '4', '8', '2', '1', '7', '0', '0', '7', '5', '4', '7', '3', '4', '0', '7', '1', '1', '6', '3', '7', '0', '4', '6', '9', '4', '8', '8', '8', '8', '1', '5', '2', '6', '4', '6', '3', '3', '1', '9', '6', '4', '6', '5', '1', '1', '2', '1', '9', '4', '5', '6', '4', '7', '9', '6', '6', '4', '6', '0', '7', '6', '4', '9', '5', '2', '4', '5', '0', '7', '0', '7', '7', '1', '1', '9', '7', '5', '4', '4', '2', '3', '9', '0', '1', '8', '1', '6', '4', '2', '3', '4', '1', '2', '2', '3', '3', '9', '1', '3', '0', '3', '4', '0', '8', '0', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow042_jensenBoundDenominatorChars : List Char := ['1', '0', '7', '6', '2', '9', '6', '5', '3', '2', '3', '3', '9', '3', '9', '9', '7', '7', '8', '6', '8', '7', '9', '3', '8', '5', '4', '0', '9', '8', '1', '9', '4', '2', '6', '5', '9', '4', '2', '4', '2', '0', '0', '3', '6', '0', '4', '5', '9', '8', '4', '8', '8', '3', '4', '8', '4', '2', '4', '1', '0', '4', '0', '9', '4', '3', '6', '7', '7', '2', '8', '9', '8', '0', '0', '5', '3', '5', '6', '7', '9', '3', '9', '6', '7', '8', '6', '0', '0', '8', '4', '9', '8', '3', '4', '1', '2', '8', '1', '2', '0', '9', '0', '9', '6', '6', '7', '4', '1', '1', '0', '1', '8', '3', '7', '9', '9', '8', '8', '3', '5', '4', '0', '4', '5', '1', '3', '3', '9', '0', '3', '1', '3', '5', '8', '3', '9', '6', '8', '2', '5', '6', '4', '5', '9', '9', '1', '3', '3', '3', '3', '7', '3', '5', '1', '5', '5', '0', '0', '0', '9', '9', '2', '3', '4', '3', '6', '0', '5', '7', '1', '7', '0', '2', '4', '9', '8', '5', '4', '3', '6', '8', '5', '2', '0', '7', '8', '6', '2', '8', '8', '1', '6', '9', '6', '5', '2', '2', '3', '6', '8', '7', '9', '2', '9', '9', '6', '1']
noncomputable def geometryRow042_jensenBoundText : String := String.ofList (geometryRow042_jensenBoundNumeratorChars ++ '/' :: geometryRow042_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_jensenBound_before_field"
  err.flush

theorem geometryRow042_jensenBound_field :
    geometryRowsJson042.getObjVal? "jensen_bound" = .ok (.str geometryRow042_jensenBoundText) := by rfl

theorem geometryRow042_jensenBound_numerator_no_slash :
    geometryRow042_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow042_jensenBoundNumeratorChars = some (170634162783436087262404841015991523640018248987029120200313645525482170075473407116370469488881526463319646511219456479664607649524507077119754423901816423412233913034080256000000000000000000000 : Int) := by decide +kernel

theorem geometryRow042_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow042_jensenBoundDenominatorChars = some (1076296532339399778687938540981942659424200360459848834842410409436772898005356793967860084983412812090966741101837998835404513390313583968256459913333735155000992343605717024985436852078628816965223687929961 : Int) := by decide +kernel

theorem geometryRow042_jensenBound_denominator_nonzero : (1076296532339399778687938540981942659424200360459848834842410409436772898005356793967860084983412812090966741101837998835404513390313583968256459913333735155000992343605717024985436852078628816965223687929961 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_jensenBound_parse :
    parseRational geometryRow042_jensenBoundText = .ok geometryRowsTyped042.jensenBound :=
  original_rational_fraction_of_chars geometryRow042_jensenBoundNumeratorChars geometryRow042_jensenBoundDenominatorChars
    (170634162783436087262404841015991523640018248987029120200313645525482170075473407116370469488881526463319646511219456479664607649524507077119754423901816423412233913034080256000000000000000000000 : Int) (1076296532339399778687938540981942659424200360459848834842410409436772898005356793967860084983412812090966741101837998835404513390313583968256459913333735155000992343605717024985436852078628816965223687929961 : Int)
    geometryRow042_jensenBound_numerator_no_slash geometryRow042_jensenBound_numerator_parse
    geometryRow042_jensenBound_denominator_parse geometryRow042_jensenBound_denominator_nonzero

theorem geometryRow042_jensenBound_read :
    rationalField geometryRowsJson042 "jensen_bound" = .ok geometryRowsTyped042.jensenBound :=
  original_rationalField_of_string geometryRowsJson042 "jensen_bound" geometryRow042_jensenBoundText
    geometryRowsTyped042.jensenBound geometryRow042_jensenBound_field geometryRow042_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_factorMaxima_before"
  err.flush

theorem geometryRow042_factorMaxima_read :
    rationalArrayField geometryRowsJson042 "factor_maxima" = .ok geometryRowsTyped042.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_gapWeightedMeans_before"
  err.flush

theorem geometryRow042_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson042 "gap_weighted_means" = .ok geometryRowsTyped042.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow042_floorChars : List Char := ['1', '2', '5', '6', '0', '6', '9', '3', '7', '9', '8', '8', '6', '1', '3', '8', '4']
noncomputable def geometryRow042_floorText : String := String.ofList geometryRow042_floorChars

theorem geometryRow042_floor_text_read :
    geometryRowsJson042.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow042_floorText := by rfl

theorem geometryRow042_floor_chars_parse :
    SourceJson.intChars geometryRow042_floorChars = some (12560693798861384 : Int) := by decide +kernel

theorem geometryRow042_floor_parse :
    parseInteger geometryRow042_floorText = .ok geometryRowsTyped042.jensenFloorQ96 := by
  simp only [geometryRow042_floorText, parseInteger, String.toList_ofList, geometryRow042_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_042 :
    decodeGeometryRow geometryRowsJson042 = .ok geometryRowsTyped042 :=
  original_geometryRow_of_fields geometryRowsJson042 geometryRowsTyped042 geometryRow042_floorText
    geometryRow042_simplexId_read geometryRow042_vertexIds_read
    geometryRow042_physicalVolume_read geometryRow042_meanGap_read
    geometryRow042_factorMaxima_read geometryRow042_gapWeightedMeans_read
    geometryRow042_jensenBound_read geometryRow042_floor_text_read geometryRow042_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_042_original_decoder_complete"
  err.flush

theorem geometryRow042_shape :
    geometryRowsTyped042.simplexId = 42 ∧
    geometryRowsTyped042.vertexIds.size = 9 ∧ geometryRowsTyped042.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped042.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped042.factorMaxima.size = 10 ∧ geometryRowsTyped042.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson043 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped043 : GeometryRow :=
  { simplexId := 43,
    vertexIds := #[27, 25, 24, 10, 8, 7, 5, 3, 1],
    physicalVolume := ((5210516899313797406240800128386356667 : ℚ) / (294956908904448000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((4766067610067 : ℚ) / (52264800000000 : ℚ)), ((4791277766927 : ℚ) / (52264800000000 : ℚ)), ((1255012762049 : ℚ) / (10452960000000 : ℚ)), ((384026455333 : ℚ) / (4355400000000 : ℚ)), ((4442964854119 : ℚ) / (52264800000000 : ℚ)), ((773665706719 : ℚ) / (10452960000000 : ℚ)), ((336706990351 : ℚ) / (8710800000000 : ℚ)), ((894281305007 : ℚ) / (26132400000000 : ℚ)), ((1717278158209 : ℚ) / (52264800000000 : ℚ)), ((1717271189569 : ℚ) / (52264800000000 : ℚ))],
    jensenBound := ((799956560379672070992320562577957437901411030141185710619526886414949030537056256000000000000000000000000 : ℚ) / (33593315849427771719331158819923795818315675203207344232265512862033254269029063614269282985852659593925188534562896561001 : ℚ)),
    jensenFloorQ96 := (1886657710545 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_simplexId_before"
  err.flush

theorem geometryRow043_simplexId_read :
    geometryRowsJson043.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped043.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_vertexIds_before"
  err.flush

theorem geometryRow043_vertexIds_read :
    geometryRowsJson043.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped043.vertexIds := by decide +kernel

noncomputable def geometryRow043_physicalVolumeNumeratorChars : List Char := ['5', '2', '1', '0', '5', '1', '6', '8', '9', '9', '3', '1', '3', '7', '9', '7', '4', '0', '6', '2', '4', '0', '8', '0', '0', '1', '2', '8', '3', '8', '6', '3', '5', '6', '6', '6', '7']
noncomputable def geometryRow043_physicalVolumeDenominatorChars : List Char := ['2', '9', '4', '9', '5', '6', '9', '0', '8', '9', '0', '4', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_physicalVolumeText : String := String.ofList (geometryRow043_physicalVolumeNumeratorChars ++ '/' :: geometryRow043_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_physicalVolume_before_field"
  err.flush

theorem geometryRow043_physicalVolume_field :
    geometryRowsJson043.getObjVal? "physical_volume" = .ok (.str geometryRow043_physicalVolumeText) := by rfl

theorem geometryRow043_physicalVolume_numerator_no_slash :
    geometryRow043_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow043_physicalVolumeNumeratorChars = some (5210516899313797406240800128386356667 : Int) := by decide +kernel

theorem geometryRow043_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow043_physicalVolumeDenominatorChars = some (294956908904448000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow043_physicalVolume_denominator_nonzero : (294956908904448000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_physicalVolume_parse :
    parseRational geometryRow043_physicalVolumeText = .ok geometryRowsTyped043.physicalVolume :=
  original_rational_fraction_of_chars geometryRow043_physicalVolumeNumeratorChars geometryRow043_physicalVolumeDenominatorChars
    (5210516899313797406240800128386356667 : Int) (294956908904448000000000000000000000000000000000000000000000000 : Int)
    geometryRow043_physicalVolume_numerator_no_slash geometryRow043_physicalVolume_numerator_parse
    geometryRow043_physicalVolume_denominator_parse geometryRow043_physicalVolume_denominator_nonzero

theorem geometryRow043_physicalVolume_read :
    rationalField geometryRowsJson043 "physical_volume" = .ok geometryRowsTyped043.physicalVolume :=
  original_rationalField_of_string geometryRowsJson043 "physical_volume" geometryRow043_physicalVolumeText
    geometryRowsTyped043.physicalVolume geometryRow043_physicalVolume_field geometryRow043_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_physicalVolume_complete"
  err.flush

noncomputable def geometryRow043_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow043_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_meanGapText : String := String.ofList (geometryRow043_meanGapNumeratorChars ++ '/' :: geometryRow043_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_meanGap_before_field"
  err.flush

theorem geometryRow043_meanGap_field :
    geometryRowsJson043.getObjVal? "mean_gap" = .ok (.str geometryRow043_meanGapText) := by rfl

theorem geometryRow043_meanGap_numerator_no_slash :
    geometryRow043_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_meanGap_numerator_parse :
    SourceJson.intChars geometryRow043_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow043_meanGap_denominator_parse :
    SourceJson.intChars geometryRow043_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow043_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_meanGap_parse :
    parseRational geometryRow043_meanGapText = .ok geometryRowsTyped043.meanGap :=
  original_rational_fraction_of_chars geometryRow043_meanGapNumeratorChars geometryRow043_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow043_meanGap_numerator_no_slash geometryRow043_meanGap_numerator_parse
    geometryRow043_meanGap_denominator_parse geometryRow043_meanGap_denominator_nonzero

theorem geometryRow043_meanGap_read :
    rationalField geometryRowsJson043 "mean_gap" = .ok geometryRowsTyped043.meanGap :=
  original_rationalField_of_string geometryRowsJson043 "mean_gap" geometryRow043_meanGapText
    geometryRowsTyped043.meanGap geometryRow043_meanGap_field geometryRow043_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_meanGap_complete"
  err.flush

noncomputable def geometryRow043_jensenBoundNumeratorChars : List Char := ['7', '9', '9', '9', '5', '6', '5', '6', '0', '3', '7', '9', '6', '7', '2', '0', '7', '0', '9', '9', '2', '3', '2', '0', '5', '6', '2', '5', '7', '7', '9', '5', '7', '4', '3', '7', '9', '0', '1', '4', '1', '1', '0', '3', '0', '1', '4', '1', '1', '8', '5', '7', '1', '0', '6', '1', '9', '5', '2', '6', '8', '8', '6', '4', '1', '4', '9', '4', '9', '0', '3', '0', '5', '3', '7', '0', '5', '6', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_jensenBoundDenominatorChars : List Char := ['3', '3', '5', '9', '3', '3', '1', '5', '8', '4', '9', '4', '2', '7', '7', '7', '1', '7', '1', '9', '3', '3', '1', '1', '5', '8', '8', '1', '9', '9', '2', '3', '7', '9', '5', '8', '1', '8', '3', '1', '5', '6', '7', '5', '2', '0', '3', '2', '0', '7', '3', '4', '4', '2', '3', '2', '2', '6', '5', '5', '1', '2', '8', '6', '2', '0', '3', '3', '2', '5', '4', '2', '6', '9', '0', '2', '9', '0', '6', '3', '6', '1', '4', '2', '6', '9', '2', '8', '2', '9', '8', '5', '8', '5', '2', '6', '5', '9', '5', '9', '3', '9', '2', '5', '1', '8', '8', '5', '3', '4', '5', '6', '2', '8', '9', '6', '5', '6', '1', '0', '0', '1']
noncomputable def geometryRow043_jensenBoundText : String := String.ofList (geometryRow043_jensenBoundNumeratorChars ++ '/' :: geometryRow043_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_jensenBound_before_field"
  err.flush

theorem geometryRow043_jensenBound_field :
    geometryRowsJson043.getObjVal? "jensen_bound" = .ok (.str geometryRow043_jensenBoundText) := by rfl

theorem geometryRow043_jensenBound_numerator_no_slash :
    geometryRow043_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow043_jensenBoundNumeratorChars = some (799956560379672070992320562577957437901411030141185710619526886414949030537056256000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow043_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow043_jensenBoundDenominatorChars = some (33593315849427771719331158819923795818315675203207344232265512862033254269029063614269282985852659593925188534562896561001 : Int) := by decide +kernel

theorem geometryRow043_jensenBound_denominator_nonzero : (33593315849427771719331158819923795818315675203207344232265512862033254269029063614269282985852659593925188534562896561001 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_jensenBound_parse :
    parseRational geometryRow043_jensenBoundText = .ok geometryRowsTyped043.jensenBound :=
  original_rational_fraction_of_chars geometryRow043_jensenBoundNumeratorChars geometryRow043_jensenBoundDenominatorChars
    (799956560379672070992320562577957437901411030141185710619526886414949030537056256000000000000000000000000 : Int) (33593315849427771719331158819923795818315675203207344232265512862033254269029063614269282985852659593925188534562896561001 : Int)
    geometryRow043_jensenBound_numerator_no_slash geometryRow043_jensenBound_numerator_parse
    geometryRow043_jensenBound_denominator_parse geometryRow043_jensenBound_denominator_nonzero

theorem geometryRow043_jensenBound_read :
    rationalField geometryRowsJson043 "jensen_bound" = .ok geometryRowsTyped043.jensenBound :=
  original_rationalField_of_string geometryRowsJson043 "jensen_bound" geometryRow043_jensenBoundText
    geometryRowsTyped043.jensenBound geometryRow043_jensenBound_field geometryRow043_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_factorMaxima_before"
  err.flush

theorem geometryRow043_factorMaxima_read :
    rationalArrayField geometryRowsJson043 "factor_maxima" = .ok geometryRowsTyped043.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_gapWeightedMeans_before"
  err.flush

theorem geometryRow043_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson043 "gap_weighted_means" = .ok geometryRowsTyped043.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow043_floorChars : List Char := ['1', '8', '8', '6', '6', '5', '7', '7', '1', '0', '5', '4', '5']
noncomputable def geometryRow043_floorText : String := String.ofList geometryRow043_floorChars

theorem geometryRow043_floor_text_read :
    geometryRowsJson043.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow043_floorText := by rfl

theorem geometryRow043_floor_chars_parse :
    SourceJson.intChars geometryRow043_floorChars = some (1886657710545 : Int) := by decide +kernel

theorem geometryRow043_floor_parse :
    parseInteger geometryRow043_floorText = .ok geometryRowsTyped043.jensenFloorQ96 := by
  simp only [geometryRow043_floorText, parseInteger, String.toList_ofList, geometryRow043_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_043 :
    decodeGeometryRow geometryRowsJson043 = .ok geometryRowsTyped043 :=
  original_geometryRow_of_fields geometryRowsJson043 geometryRowsTyped043 geometryRow043_floorText
    geometryRow043_simplexId_read geometryRow043_vertexIds_read
    geometryRow043_physicalVolume_read geometryRow043_meanGap_read
    geometryRow043_factorMaxima_read geometryRow043_gapWeightedMeans_read
    geometryRow043_jensenBound_read geometryRow043_floor_text_read geometryRow043_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_043_original_decoder_complete"
  err.flush

theorem geometryRow043_shape :
    geometryRowsTyped043.simplexId = 43 ∧
    geometryRowsTyped043.vertexIds.size = 9 ∧ geometryRowsTyped043.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped043.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped043.factorMaxima.size = 10 ∧ geometryRowsTyped043.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson044 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped044 : GeometryRow :=
  { simplexId := 44,
    vertexIds := #[27, 25, 24, 23, 10, 7, 5, 3, 1],
    physicalVolume := ((467874210547785174228896929659981791 : ℚ) / (40381005385728000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((108925326048541 : ℚ) / (1202090400000000 : ℚ)), ((109505159656321 : ℚ) / (1202090400000000 : ℚ)), ((29134744180879 : ℚ) / (240418080000000 : ℚ)), ((1509238970289 : ℚ) / (16695700000000 : ℚ)), ((104209071547877 : ℚ) / (1202090400000000 : ℚ)), ((3504972120157 : ℚ) / (48083616000000 : ℚ)), ((7631989672343 : ℚ) / (200348400000000 : ℚ)), ((20231656697971 : ℚ) / (601045200000000 : ℚ)), ((38170746718667 : ℚ) / (1202090400000000 : ℚ)), ((38170586439947 : ℚ) / (1202090400000000 : ℚ))],
    jensenBound := ((7318432296351757406524547927899419411351128660599155126034419097272793759250192854361790873600000000000000000000000 : ℚ) / (435327677824186502193713470595433654041367074532151134273063253110892486963897376352070452954959116484185107724195498009060361887997 : ℚ)),
    jensenFloorQ96 := (1331929883767 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_simplexId_before"
  err.flush

theorem geometryRow044_simplexId_read :
    geometryRowsJson044.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped044.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_vertexIds_before"
  err.flush

theorem geometryRow044_vertexIds_read :
    geometryRowsJson044.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped044.vertexIds := by decide +kernel

noncomputable def geometryRow044_physicalVolumeNumeratorChars : List Char := ['4', '6', '7', '8', '7', '4', '2', '1', '0', '5', '4', '7', '7', '8', '5', '1', '7', '4', '2', '2', '8', '8', '9', '6', '9', '2', '9', '6', '5', '9', '9', '8', '1', '7', '9', '1']
noncomputable def geometryRow044_physicalVolumeDenominatorChars : List Char := ['4', '0', '3', '8', '1', '0', '0', '5', '3', '8', '5', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_physicalVolumeText : String := String.ofList (geometryRow044_physicalVolumeNumeratorChars ++ '/' :: geometryRow044_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_physicalVolume_before_field"
  err.flush

theorem geometryRow044_physicalVolume_field :
    geometryRowsJson044.getObjVal? "physical_volume" = .ok (.str geometryRow044_physicalVolumeText) := by rfl

theorem geometryRow044_physicalVolume_numerator_no_slash :
    geometryRow044_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow044_physicalVolumeNumeratorChars = some (467874210547785174228896929659981791 : Int) := by decide +kernel

theorem geometryRow044_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow044_physicalVolumeDenominatorChars = some (40381005385728000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow044_physicalVolume_denominator_nonzero : (40381005385728000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_physicalVolume_parse :
    parseRational geometryRow044_physicalVolumeText = .ok geometryRowsTyped044.physicalVolume :=
  original_rational_fraction_of_chars geometryRow044_physicalVolumeNumeratorChars geometryRow044_physicalVolumeDenominatorChars
    (467874210547785174228896929659981791 : Int) (40381005385728000000000000000000000000000000000000000000000000 : Int)
    geometryRow044_physicalVolume_numerator_no_slash geometryRow044_physicalVolume_numerator_parse
    geometryRow044_physicalVolume_denominator_parse geometryRow044_physicalVolume_denominator_nonzero

theorem geometryRow044_physicalVolume_read :
    rationalField geometryRowsJson044 "physical_volume" = .ok geometryRowsTyped044.physicalVolume :=
  original_rationalField_of_string geometryRowsJson044 "physical_volume" geometryRow044_physicalVolumeText
    geometryRowsTyped044.physicalVolume geometryRow044_physicalVolume_field geometryRow044_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_physicalVolume_complete"
  err.flush

noncomputable def geometryRow044_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow044_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_meanGapText : String := String.ofList (geometryRow044_meanGapNumeratorChars ++ '/' :: geometryRow044_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_meanGap_before_field"
  err.flush

theorem geometryRow044_meanGap_field :
    geometryRowsJson044.getObjVal? "mean_gap" = .ok (.str geometryRow044_meanGapText) := by rfl

theorem geometryRow044_meanGap_numerator_no_slash :
    geometryRow044_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_meanGap_numerator_parse :
    SourceJson.intChars geometryRow044_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow044_meanGap_denominator_parse :
    SourceJson.intChars geometryRow044_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow044_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_meanGap_parse :
    parseRational geometryRow044_meanGapText = .ok geometryRowsTyped044.meanGap :=
  original_rational_fraction_of_chars geometryRow044_meanGapNumeratorChars geometryRow044_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow044_meanGap_numerator_no_slash geometryRow044_meanGap_numerator_parse
    geometryRow044_meanGap_denominator_parse geometryRow044_meanGap_denominator_nonzero

theorem geometryRow044_meanGap_read :
    rationalField geometryRowsJson044 "mean_gap" = .ok geometryRowsTyped044.meanGap :=
  original_rationalField_of_string geometryRowsJson044 "mean_gap" geometryRow044_meanGapText
    geometryRowsTyped044.meanGap geometryRow044_meanGap_field geometryRow044_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_meanGap_complete"
  err.flush

noncomputable def geometryRow044_jensenBoundNumeratorChars : List Char := ['7', '3', '1', '8', '4', '3', '2', '2', '9', '6', '3', '5', '1', '7', '5', '7', '4', '0', '6', '5', '2', '4', '5', '4', '7', '9', '2', '7', '8', '9', '9', '4', '1', '9', '4', '1', '1', '3', '5', '1', '1', '2', '8', '6', '6', '0', '5', '9', '9', '1', '5', '5', '1', '2', '6', '0', '3', '4', '4', '1', '9', '0', '9', '7', '2', '7', '2', '7', '9', '3', '7', '5', '9', '2', '5', '0', '1', '9', '2', '8', '5', '4', '3', '6', '1', '7', '9', '0', '8', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_jensenBoundDenominatorChars : List Char := ['4', '3', '5', '3', '2', '7', '6', '7', '7', '8', '2', '4', '1', '8', '6', '5', '0', '2', '1', '9', '3', '7', '1', '3', '4', '7', '0', '5', '9', '5', '4', '3', '3', '6', '5', '4', '0', '4', '1', '3', '6', '7', '0', '7', '4', '5', '3', '2', '1', '5', '1', '1', '3', '4', '2', '7', '3', '0', '6', '3', '2', '5', '3', '1', '1', '0', '8', '9', '2', '4', '8', '6', '9', '6', '3', '8', '9', '7', '3', '7', '6', '3', '5', '2', '0', '7', '0', '4', '5', '2', '9', '5', '4', '9', '5', '9', '1', '1', '6', '4', '8', '4', '1', '8', '5', '1', '0', '7', '7', '2', '4', '1', '9', '5', '4', '9', '8', '0', '0', '9', '0', '6', '0', '3', '6', '1', '8', '8', '7', '9', '9', '7']
noncomputable def geometryRow044_jensenBoundText : String := String.ofList (geometryRow044_jensenBoundNumeratorChars ++ '/' :: geometryRow044_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_jensenBound_before_field"
  err.flush

theorem geometryRow044_jensenBound_field :
    geometryRowsJson044.getObjVal? "jensen_bound" = .ok (.str geometryRow044_jensenBoundText) := by rfl

theorem geometryRow044_jensenBound_numerator_no_slash :
    geometryRow044_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow044_jensenBoundNumeratorChars = some (7318432296351757406524547927899419411351128660599155126034419097272793759250192854361790873600000000000000000000000 : Int) := by decide +kernel

theorem geometryRow044_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow044_jensenBoundDenominatorChars = some (435327677824186502193713470595433654041367074532151134273063253110892486963897376352070452954959116484185107724195498009060361887997 : Int) := by decide +kernel

theorem geometryRow044_jensenBound_denominator_nonzero : (435327677824186502193713470595433654041367074532151134273063253110892486963897376352070452954959116484185107724195498009060361887997 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_jensenBound_parse :
    parseRational geometryRow044_jensenBoundText = .ok geometryRowsTyped044.jensenBound :=
  original_rational_fraction_of_chars geometryRow044_jensenBoundNumeratorChars geometryRow044_jensenBoundDenominatorChars
    (7318432296351757406524547927899419411351128660599155126034419097272793759250192854361790873600000000000000000000000 : Int) (435327677824186502193713470595433654041367074532151134273063253110892486963897376352070452954959116484185107724195498009060361887997 : Int)
    geometryRow044_jensenBound_numerator_no_slash geometryRow044_jensenBound_numerator_parse
    geometryRow044_jensenBound_denominator_parse geometryRow044_jensenBound_denominator_nonzero

theorem geometryRow044_jensenBound_read :
    rationalField geometryRowsJson044 "jensen_bound" = .ok geometryRowsTyped044.jensenBound :=
  original_rationalField_of_string geometryRowsJson044 "jensen_bound" geometryRow044_jensenBoundText
    geometryRowsTyped044.jensenBound geometryRow044_jensenBound_field geometryRow044_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_factorMaxima_before"
  err.flush

theorem geometryRow044_factorMaxima_read :
    rationalArrayField geometryRowsJson044 "factor_maxima" = .ok geometryRowsTyped044.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_gapWeightedMeans_before"
  err.flush

theorem geometryRow044_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson044 "gap_weighted_means" = .ok geometryRowsTyped044.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow044_floorChars : List Char := ['1', '3', '3', '1', '9', '2', '9', '8', '8', '3', '7', '6', '7']
noncomputable def geometryRow044_floorText : String := String.ofList geometryRow044_floorChars

theorem geometryRow044_floor_text_read :
    geometryRowsJson044.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow044_floorText := by rfl

theorem geometryRow044_floor_chars_parse :
    SourceJson.intChars geometryRow044_floorChars = some (1331929883767 : Int) := by decide +kernel

theorem geometryRow044_floor_parse :
    parseInteger geometryRow044_floorText = .ok geometryRowsTyped044.jensenFloorQ96 := by
  simp only [geometryRow044_floorText, parseInteger, String.toList_ofList, geometryRow044_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_044 :
    decodeGeometryRow geometryRowsJson044 = .ok geometryRowsTyped044 :=
  original_geometryRow_of_fields geometryRowsJson044 geometryRowsTyped044 geometryRow044_floorText
    geometryRow044_simplexId_read geometryRow044_vertexIds_read
    geometryRow044_physicalVolume_read geometryRow044_meanGap_read
    geometryRow044_factorMaxima_read geometryRow044_gapWeightedMeans_read
    geometryRow044_jensenBound_read geometryRow044_floor_text_read geometryRow044_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_044_original_decoder_complete"
  err.flush

theorem geometryRow044_shape :
    geometryRowsTyped044.simplexId = 44 ∧
    geometryRowsTyped044.vertexIds.size = 9 ∧ geometryRowsTyped044.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped044.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped044.factorMaxima.size = 10 ∧ geometryRowsTyped044.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson045 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped045 : GeometryRow :=
  { simplexId := 45,
    vertexIds := #[27, 25, 24, 23, 21, 7, 5, 3, 1],
    physicalVolume := ((13143642418970170025456179293669149 : ℚ) / (1352042591040000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((53984700611633 : ℚ) / (601045200000000 : ℚ)), ((54274617415523 : ℚ) / (601045200000000 : ℚ)), ((29376208079527 : ℚ) / (240418080000000 : ℚ)), ((36730388987491 : ℚ) / (400696800000000 : ℚ)), ((106556463593897 : ℚ) / (1202090400000000 : ℚ)), ((17283396702137 : ℚ) / (240418080000000 : ℚ)), ((7441977580213 : ℚ) / (200348400000000 : ℚ)), ((19661620421581 : ℚ) / (601045200000000 : ℚ)), ((18926052555121 : ℚ) / (601045200000000 : ℚ)), ((18925972415761 : ℚ) / (601045200000000 : ℚ))],
    jensenBound := ((37679274332589575760708165826146103762134268536068090303266471067740379703379292335180244582400000000000000000000000 : ℚ) / (2521959845604423461657092194516522940671143435993610414564877540343303991516532394368745544904747547575806352932075928288811258993431 : ℚ)),
    jensenFloorQ96 := (1183706265365 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_simplexId_before"
  err.flush

theorem geometryRow045_simplexId_read :
    geometryRowsJson045.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped045.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_vertexIds_before"
  err.flush

theorem geometryRow045_vertexIds_read :
    geometryRowsJson045.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped045.vertexIds := by decide +kernel

noncomputable def geometryRow045_physicalVolumeNumeratorChars : List Char := ['1', '3', '1', '4', '3', '6', '4', '2', '4', '1', '8', '9', '7', '0', '1', '7', '0', '0', '2', '5', '4', '5', '6', '1', '7', '9', '2', '9', '3', '6', '6', '9', '1', '4', '9']
noncomputable def geometryRow045_physicalVolumeDenominatorChars : List Char := ['1', '3', '5', '2', '0', '4', '2', '5', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_physicalVolumeText : String := String.ofList (geometryRow045_physicalVolumeNumeratorChars ++ '/' :: geometryRow045_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_physicalVolume_before_field"
  err.flush

theorem geometryRow045_physicalVolume_field :
    geometryRowsJson045.getObjVal? "physical_volume" = .ok (.str geometryRow045_physicalVolumeText) := by rfl

theorem geometryRow045_physicalVolume_numerator_no_slash :
    geometryRow045_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow045_physicalVolumeNumeratorChars = some (13143642418970170025456179293669149 : Int) := by decide +kernel

theorem geometryRow045_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow045_physicalVolumeDenominatorChars = some (1352042591040000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow045_physicalVolume_denominator_nonzero : (1352042591040000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_physicalVolume_parse :
    parseRational geometryRow045_physicalVolumeText = .ok geometryRowsTyped045.physicalVolume :=
  original_rational_fraction_of_chars geometryRow045_physicalVolumeNumeratorChars geometryRow045_physicalVolumeDenominatorChars
    (13143642418970170025456179293669149 : Int) (1352042591040000000000000000000000000000000000000000000000000 : Int)
    geometryRow045_physicalVolume_numerator_no_slash geometryRow045_physicalVolume_numerator_parse
    geometryRow045_physicalVolume_denominator_parse geometryRow045_physicalVolume_denominator_nonzero

theorem geometryRow045_physicalVolume_read :
    rationalField geometryRowsJson045 "physical_volume" = .ok geometryRowsTyped045.physicalVolume :=
  original_rationalField_of_string geometryRowsJson045 "physical_volume" geometryRow045_physicalVolumeText
    geometryRowsTyped045.physicalVolume geometryRow045_physicalVolume_field geometryRow045_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_physicalVolume_complete"
  err.flush

noncomputable def geometryRow045_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow045_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_meanGapText : String := String.ofList (geometryRow045_meanGapNumeratorChars ++ '/' :: geometryRow045_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_meanGap_before_field"
  err.flush

theorem geometryRow045_meanGap_field :
    geometryRowsJson045.getObjVal? "mean_gap" = .ok (.str geometryRow045_meanGapText) := by rfl

theorem geometryRow045_meanGap_numerator_no_slash :
    geometryRow045_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_meanGap_numerator_parse :
    SourceJson.intChars geometryRow045_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow045_meanGap_denominator_parse :
    SourceJson.intChars geometryRow045_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow045_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_meanGap_parse :
    parseRational geometryRow045_meanGapText = .ok geometryRowsTyped045.meanGap :=
  original_rational_fraction_of_chars geometryRow045_meanGapNumeratorChars geometryRow045_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow045_meanGap_numerator_no_slash geometryRow045_meanGap_numerator_parse
    geometryRow045_meanGap_denominator_parse geometryRow045_meanGap_denominator_nonzero

theorem geometryRow045_meanGap_read :
    rationalField geometryRowsJson045 "mean_gap" = .ok geometryRowsTyped045.meanGap :=
  original_rationalField_of_string geometryRowsJson045 "mean_gap" geometryRow045_meanGapText
    geometryRowsTyped045.meanGap geometryRow045_meanGap_field geometryRow045_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_meanGap_complete"
  err.flush

noncomputable def geometryRow045_jensenBoundNumeratorChars : List Char := ['3', '7', '6', '7', '9', '2', '7', '4', '3', '3', '2', '5', '8', '9', '5', '7', '5', '7', '6', '0', '7', '0', '8', '1', '6', '5', '8', '2', '6', '1', '4', '6', '1', '0', '3', '7', '6', '2', '1', '3', '4', '2', '6', '8', '5', '3', '6', '0', '6', '8', '0', '9', '0', '3', '0', '3', '2', '6', '6', '4', '7', '1', '0', '6', '7', '7', '4', '0', '3', '7', '9', '7', '0', '3', '3', '7', '9', '2', '9', '2', '3', '3', '5', '1', '8', '0', '2', '4', '4', '5', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_jensenBoundDenominatorChars : List Char := ['2', '5', '2', '1', '9', '5', '9', '8', '4', '5', '6', '0', '4', '4', '2', '3', '4', '6', '1', '6', '5', '7', '0', '9', '2', '1', '9', '4', '5', '1', '6', '5', '2', '2', '9', '4', '0', '6', '7', '1', '1', '4', '3', '4', '3', '5', '9', '9', '3', '6', '1', '0', '4', '1', '4', '5', '6', '4', '8', '7', '7', '5', '4', '0', '3', '4', '3', '3', '0', '3', '9', '9', '1', '5', '1', '6', '5', '3', '2', '3', '9', '4', '3', '6', '8', '7', '4', '5', '5', '4', '4', '9', '0', '4', '7', '4', '7', '5', '4', '7', '5', '7', '5', '8', '0', '6', '3', '5', '2', '9', '3', '2', '0', '7', '5', '9', '2', '8', '2', '8', '8', '8', '1', '1', '2', '5', '8', '9', '9', '3', '4', '3', '1']
noncomputable def geometryRow045_jensenBoundText : String := String.ofList (geometryRow045_jensenBoundNumeratorChars ++ '/' :: geometryRow045_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_jensenBound_before_field"
  err.flush

theorem geometryRow045_jensenBound_field :
    geometryRowsJson045.getObjVal? "jensen_bound" = .ok (.str geometryRow045_jensenBoundText) := by rfl

theorem geometryRow045_jensenBound_numerator_no_slash :
    geometryRow045_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow045_jensenBoundNumeratorChars = some (37679274332589575760708165826146103762134268536068090303266471067740379703379292335180244582400000000000000000000000 : Int) := by decide +kernel

theorem geometryRow045_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow045_jensenBoundDenominatorChars = some (2521959845604423461657092194516522940671143435993610414564877540343303991516532394368745544904747547575806352932075928288811258993431 : Int) := by decide +kernel

theorem geometryRow045_jensenBound_denominator_nonzero : (2521959845604423461657092194516522940671143435993610414564877540343303991516532394368745544904747547575806352932075928288811258993431 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_jensenBound_parse :
    parseRational geometryRow045_jensenBoundText = .ok geometryRowsTyped045.jensenBound :=
  original_rational_fraction_of_chars geometryRow045_jensenBoundNumeratorChars geometryRow045_jensenBoundDenominatorChars
    (37679274332589575760708165826146103762134268536068090303266471067740379703379292335180244582400000000000000000000000 : Int) (2521959845604423461657092194516522940671143435993610414564877540343303991516532394368745544904747547575806352932075928288811258993431 : Int)
    geometryRow045_jensenBound_numerator_no_slash geometryRow045_jensenBound_numerator_parse
    geometryRow045_jensenBound_denominator_parse geometryRow045_jensenBound_denominator_nonzero

theorem geometryRow045_jensenBound_read :
    rationalField geometryRowsJson045 "jensen_bound" = .ok geometryRowsTyped045.jensenBound :=
  original_rationalField_of_string geometryRowsJson045 "jensen_bound" geometryRow045_jensenBoundText
    geometryRowsTyped045.jensenBound geometryRow045_jensenBound_field geometryRow045_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_factorMaxima_before"
  err.flush

theorem geometryRow045_factorMaxima_read :
    rationalArrayField geometryRowsJson045 "factor_maxima" = .ok geometryRowsTyped045.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_gapWeightedMeans_before"
  err.flush

theorem geometryRow045_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson045 "gap_weighted_means" = .ok geometryRowsTyped045.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow045_floorChars : List Char := ['1', '1', '8', '3', '7', '0', '6', '2', '6', '5', '3', '6', '5']
noncomputable def geometryRow045_floorText : String := String.ofList geometryRow045_floorChars

theorem geometryRow045_floor_text_read :
    geometryRowsJson045.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow045_floorText := by rfl

theorem geometryRow045_floor_chars_parse :
    SourceJson.intChars geometryRow045_floorChars = some (1183706265365 : Int) := by decide +kernel

theorem geometryRow045_floor_parse :
    parseInteger geometryRow045_floorText = .ok geometryRowsTyped045.jensenFloorQ96 := by
  simp only [geometryRow045_floorText, parseInteger, String.toList_ofList, geometryRow045_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_045 :
    decodeGeometryRow geometryRowsJson045 = .ok geometryRowsTyped045 :=
  original_geometryRow_of_fields geometryRowsJson045 geometryRowsTyped045 geometryRow045_floorText
    geometryRow045_simplexId_read geometryRow045_vertexIds_read
    geometryRow045_physicalVolume_read geometryRow045_meanGap_read
    geometryRow045_factorMaxima_read geometryRow045_gapWeightedMeans_read
    geometryRow045_jensenBound_read geometryRow045_floor_text_read geometryRow045_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_045_original_decoder_complete"
  err.flush

theorem geometryRow045_shape :
    geometryRowsTyped045.simplexId = 45 ∧
    geometryRowsTyped045.vertexIds.size = 9 ∧ geometryRowsTyped045.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped045.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped045.factorMaxima.size = 10 ∧ geometryRowsTyped045.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson046 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped046 : GeometryRow :=
  { simplexId := 46,
    vertexIds := #[27, 25, 24, 23, 21, 19, 7, 5, 1],
    physicalVolume := ((269244341361219715869212971659413 : ℚ) / (40373494038000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2999973 : ℚ) / (30500000 : ℚ)), ((2999973 : ℚ) / (30500000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ))],
    gapWeightedMeans := #[((1138547166591937 : ℚ) / (12922471800000000 : ℚ)), ((286195094468893 : ℚ) / (3230617950000000 : ℚ)), ((35430153708993 : ℚ) / (287166040000000 : ℚ)), ((1207315409662751 : ℚ) / (12922471800000000 : ℚ)), ((1164487458807439 : ℚ) / (12922471800000000 : ℚ)), ((20239570508387 : ℚ) / (287166040000000 : ℚ)), ((480142701023921 : ℚ) / (12922471800000000 : ℚ)), ((209552548260527 : ℚ) / (6461235900000000 : ℚ)), ((99883874437261 : ℚ) / (3230617950000000 : ℚ)), ((99883443688201 : ℚ) / (3230617950000000 : ℚ))],
    jensenBound := ((1193723294670370016724857042412025838124081175793055631559355708581673520738026623621744487478127363304000000000000000000000000 : ℚ) / (109919314362443313564253129661517854553668602759412059907465677073734884270428516154849419837628438567160595200250441457729519454880800037055311 : ℚ)),
    jensenFloorQ96 := (860417513844 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_simplexId_before"
  err.flush

theorem geometryRow046_simplexId_read :
    geometryRowsJson046.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped046.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_vertexIds_before"
  err.flush

theorem geometryRow046_vertexIds_read :
    geometryRowsJson046.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped046.vertexIds := by decide +kernel

noncomputable def geometryRow046_physicalVolumeNumeratorChars : List Char := ['2', '6', '9', '2', '4', '4', '3', '4', '1', '3', '6', '1', '2', '1', '9', '7', '1', '5', '8', '6', '9', '2', '1', '2', '9', '7', '1', '6', '5', '9', '4', '1', '3']
noncomputable def geometryRow046_physicalVolumeDenominatorChars : List Char := ['4', '0', '3', '7', '3', '4', '9', '4', '0', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_physicalVolumeText : String := String.ofList (geometryRow046_physicalVolumeNumeratorChars ++ '/' :: geometryRow046_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_physicalVolume_before_field"
  err.flush

theorem geometryRow046_physicalVolume_field :
    geometryRowsJson046.getObjVal? "physical_volume" = .ok (.str geometryRow046_physicalVolumeText) := by rfl

theorem geometryRow046_physicalVolume_numerator_no_slash :
    geometryRow046_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow046_physicalVolumeNumeratorChars = some (269244341361219715869212971659413 : Int) := by decide +kernel

theorem geometryRow046_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow046_physicalVolumeDenominatorChars = some (40373494038000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow046_physicalVolume_denominator_nonzero : (40373494038000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_physicalVolume_parse :
    parseRational geometryRow046_physicalVolumeText = .ok geometryRowsTyped046.physicalVolume :=
  original_rational_fraction_of_chars geometryRow046_physicalVolumeNumeratorChars geometryRow046_physicalVolumeDenominatorChars
    (269244341361219715869212971659413 : Int) (40373494038000000000000000000000000000000000000000000000000 : Int)
    geometryRow046_physicalVolume_numerator_no_slash geometryRow046_physicalVolume_numerator_parse
    geometryRow046_physicalVolume_denominator_parse geometryRow046_physicalVolume_denominator_nonzero

theorem geometryRow046_physicalVolume_read :
    rationalField geometryRowsJson046 "physical_volume" = .ok geometryRowsTyped046.physicalVolume :=
  original_rationalField_of_string geometryRowsJson046 "physical_volume" geometryRow046_physicalVolumeText
    geometryRowsTyped046.physicalVolume geometryRow046_physicalVolume_field geometryRow046_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_physicalVolume_complete"
  err.flush

noncomputable def geometryRow046_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow046_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_meanGapText : String := String.ofList (geometryRow046_meanGapNumeratorChars ++ '/' :: geometryRow046_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_meanGap_before_field"
  err.flush

theorem geometryRow046_meanGap_field :
    geometryRowsJson046.getObjVal? "mean_gap" = .ok (.str geometryRow046_meanGapText) := by rfl

theorem geometryRow046_meanGap_numerator_no_slash :
    geometryRow046_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_meanGap_numerator_parse :
    SourceJson.intChars geometryRow046_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow046_meanGap_denominator_parse :
    SourceJson.intChars geometryRow046_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow046_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_meanGap_parse :
    parseRational geometryRow046_meanGapText = .ok geometryRowsTyped046.meanGap :=
  original_rational_fraction_of_chars geometryRow046_meanGapNumeratorChars geometryRow046_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow046_meanGap_numerator_no_slash geometryRow046_meanGap_numerator_parse
    geometryRow046_meanGap_denominator_parse geometryRow046_meanGap_denominator_nonzero

theorem geometryRow046_meanGap_read :
    rationalField geometryRowsJson046 "mean_gap" = .ok geometryRowsTyped046.meanGap :=
  original_rationalField_of_string geometryRowsJson046 "mean_gap" geometryRow046_meanGapText
    geometryRowsTyped046.meanGap geometryRow046_meanGap_field geometryRow046_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_meanGap_complete"
  err.flush

noncomputable def geometryRow046_jensenBoundNumeratorChars : List Char := ['1', '1', '9', '3', '7', '2', '3', '2', '9', '4', '6', '7', '0', '3', '7', '0', '0', '1', '6', '7', '2', '4', '8', '5', '7', '0', '4', '2', '4', '1', '2', '0', '2', '5', '8', '3', '8', '1', '2', '4', '0', '8', '1', '1', '7', '5', '7', '9', '3', '0', '5', '5', '6', '3', '1', '5', '5', '9', '3', '5', '5', '7', '0', '8', '5', '8', '1', '6', '7', '3', '5', '2', '0', '7', '3', '8', '0', '2', '6', '6', '2', '3', '6', '2', '1', '7', '4', '4', '4', '8', '7', '4', '7', '8', '1', '2', '7', '3', '6', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_jensenBoundDenominatorChars : List Char := ['1', '0', '9', '9', '1', '9', '3', '1', '4', '3', '6', '2', '4', '4', '3', '3', '1', '3', '5', '6', '4', '2', '5', '3', '1', '2', '9', '6', '6', '1', '5', '1', '7', '8', '5', '4', '5', '5', '3', '6', '6', '8', '6', '0', '2', '7', '5', '9', '4', '1', '2', '0', '5', '9', '9', '0', '7', '4', '6', '5', '6', '7', '7', '0', '7', '3', '7', '3', '4', '8', '8', '4', '2', '7', '0', '4', '2', '8', '5', '1', '6', '1', '5', '4', '8', '4', '9', '4', '1', '9', '8', '3', '7', '6', '2', '8', '4', '3', '8', '5', '6', '7', '1', '6', '0', '5', '9', '5', '2', '0', '0', '2', '5', '0', '4', '4', '1', '4', '5', '7', '7', '2', '9', '5', '1', '9', '4', '5', '4', '8', '8', '0', '8', '0', '0', '0', '3', '7', '0', '5', '5', '3', '1', '1']
noncomputable def geometryRow046_jensenBoundText : String := String.ofList (geometryRow046_jensenBoundNumeratorChars ++ '/' :: geometryRow046_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_jensenBound_before_field"
  err.flush

theorem geometryRow046_jensenBound_field :
    geometryRowsJson046.getObjVal? "jensen_bound" = .ok (.str geometryRow046_jensenBoundText) := by rfl

theorem geometryRow046_jensenBound_numerator_no_slash :
    geometryRow046_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow046_jensenBoundNumeratorChars = some (1193723294670370016724857042412025838124081175793055631559355708581673520738026623621744487478127363304000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow046_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow046_jensenBoundDenominatorChars = some (109919314362443313564253129661517854553668602759412059907465677073734884270428516154849419837628438567160595200250441457729519454880800037055311 : Int) := by decide +kernel

theorem geometryRow046_jensenBound_denominator_nonzero : (109919314362443313564253129661517854553668602759412059907465677073734884270428516154849419837628438567160595200250441457729519454880800037055311 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_jensenBound_parse :
    parseRational geometryRow046_jensenBoundText = .ok geometryRowsTyped046.jensenBound :=
  original_rational_fraction_of_chars geometryRow046_jensenBoundNumeratorChars geometryRow046_jensenBoundDenominatorChars
    (1193723294670370016724857042412025838124081175793055631559355708581673520738026623621744487478127363304000000000000000000000000 : Int) (109919314362443313564253129661517854553668602759412059907465677073734884270428516154849419837628438567160595200250441457729519454880800037055311 : Int)
    geometryRow046_jensenBound_numerator_no_slash geometryRow046_jensenBound_numerator_parse
    geometryRow046_jensenBound_denominator_parse geometryRow046_jensenBound_denominator_nonzero

theorem geometryRow046_jensenBound_read :
    rationalField geometryRowsJson046 "jensen_bound" = .ok geometryRowsTyped046.jensenBound :=
  original_rationalField_of_string geometryRowsJson046 "jensen_bound" geometryRow046_jensenBoundText
    geometryRowsTyped046.jensenBound geometryRow046_jensenBound_field geometryRow046_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_factorMaxima_before"
  err.flush

theorem geometryRow046_factorMaxima_read :
    rationalArrayField geometryRowsJson046 "factor_maxima" = .ok geometryRowsTyped046.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_gapWeightedMeans_before"
  err.flush

theorem geometryRow046_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson046 "gap_weighted_means" = .ok geometryRowsTyped046.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow046_floorChars : List Char := ['8', '6', '0', '4', '1', '7', '5', '1', '3', '8', '4', '4']
noncomputable def geometryRow046_floorText : String := String.ofList geometryRow046_floorChars

theorem geometryRow046_floor_text_read :
    geometryRowsJson046.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow046_floorText := by rfl

theorem geometryRow046_floor_chars_parse :
    SourceJson.intChars geometryRow046_floorChars = some (860417513844 : Int) := by decide +kernel

theorem geometryRow046_floor_parse :
    parseInteger geometryRow046_floorText = .ok geometryRowsTyped046.jensenFloorQ96 := by
  simp only [geometryRow046_floorText, parseInteger, String.toList_ofList, geometryRow046_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_046 :
    decodeGeometryRow geometryRowsJson046 = .ok geometryRowsTyped046 :=
  original_geometryRow_of_fields geometryRowsJson046 geometryRowsTyped046 geometryRow046_floorText
    geometryRow046_simplexId_read geometryRow046_vertexIds_read
    geometryRow046_physicalVolume_read geometryRow046_meanGap_read
    geometryRow046_factorMaxima_read geometryRow046_gapWeightedMeans_read
    geometryRow046_jensenBound_read geometryRow046_floor_text_read geometryRow046_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_046_original_decoder_complete"
  err.flush

theorem geometryRow046_shape :
    geometryRowsTyped046.simplexId = 46 ∧
    geometryRowsTyped046.vertexIds.size = 9 ∧ geometryRowsTyped046.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped046.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped046.factorMaxima.size = 10 ∧ geometryRowsTyped046.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson047 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped047 : GeometryRow :=
  { simplexId := 47,
    vertexIds := #[27, 25, 24, 23, 21, 19, 17, 5, 1],
    physicalVolume := ((141696759349134761527771302999481 : ℚ) / (24819770925000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((12984403 : ℚ) / (136000000 : ℚ)), ((3328101 : ℚ) / (34000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((2328113 : ℚ) / (68000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ))],
    gapWeightedMeans := #[((9159425513531 : ℚ) / (105921900000000 : ℚ)), ((18421034818597 : ℚ) / (211843800000000 : ℚ)), ((1754765536169 : ℚ) / (14122920000000 : ℚ)), ((10045912920763 : ℚ) / (105921900000000 : ℚ)), ((9732834076727 : ℚ) / (105921900000000 : ℚ)), ((986886746557 : ℚ) / (14122920000000 : ℚ)), ((3967443861553 : ℚ) / (105921900000000 : ℚ)), ((6679349945209 : ℚ) / (211843800000000 : ℚ)), ((6434476717519 : ℚ) / (211843800000000 : ℚ)), ((6434448471679 : ℚ) / (211843800000000 : ℚ))],
    jensenBound := ((309436094118170089295290009413249600245608453516466365004579181545540630028356304633185280000000000000000000000 : ℚ) / (31344904396493054285118705458797244109212271590767605861764268129729450237525569179928932849817888321318552099736971364097239887 : ℚ)),
    jensenFloorQ96 := (782138392973 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_simplexId_before"
  err.flush

theorem geometryRow047_simplexId_read :
    geometryRowsJson047.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped047.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_vertexIds_before"
  err.flush

theorem geometryRow047_vertexIds_read :
    geometryRowsJson047.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped047.vertexIds := by decide +kernel

noncomputable def geometryRow047_physicalVolumeNumeratorChars : List Char := ['1', '4', '1', '6', '9', '6', '7', '5', '9', '3', '4', '9', '1', '3', '4', '7', '6', '1', '5', '2', '7', '7', '7', '1', '3', '0', '2', '9', '9', '9', '4', '8', '1']
noncomputable def geometryRow047_physicalVolumeDenominatorChars : List Char := ['2', '4', '8', '1', '9', '7', '7', '0', '9', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_physicalVolumeText : String := String.ofList (geometryRow047_physicalVolumeNumeratorChars ++ '/' :: geometryRow047_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_physicalVolume_before_field"
  err.flush

theorem geometryRow047_physicalVolume_field :
    geometryRowsJson047.getObjVal? "physical_volume" = .ok (.str geometryRow047_physicalVolumeText) := by rfl

theorem geometryRow047_physicalVolume_numerator_no_slash :
    geometryRow047_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow047_physicalVolumeNumeratorChars = some (141696759349134761527771302999481 : Int) := by decide +kernel

theorem geometryRow047_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow047_physicalVolumeDenominatorChars = some (24819770925000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow047_physicalVolume_denominator_nonzero : (24819770925000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_physicalVolume_parse :
    parseRational geometryRow047_physicalVolumeText = .ok geometryRowsTyped047.physicalVolume :=
  original_rational_fraction_of_chars geometryRow047_physicalVolumeNumeratorChars geometryRow047_physicalVolumeDenominatorChars
    (141696759349134761527771302999481 : Int) (24819770925000000000000000000000000000000000000000000000000 : Int)
    geometryRow047_physicalVolume_numerator_no_slash geometryRow047_physicalVolume_numerator_parse
    geometryRow047_physicalVolume_denominator_parse geometryRow047_physicalVolume_denominator_nonzero

theorem geometryRow047_physicalVolume_read :
    rationalField geometryRowsJson047 "physical_volume" = .ok geometryRowsTyped047.physicalVolume :=
  original_rationalField_of_string geometryRowsJson047 "physical_volume" geometryRow047_physicalVolumeText
    geometryRowsTyped047.physicalVolume geometryRow047_physicalVolume_field geometryRow047_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_physicalVolume_complete"
  err.flush

noncomputable def geometryRow047_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow047_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_meanGapText : String := String.ofList (geometryRow047_meanGapNumeratorChars ++ '/' :: geometryRow047_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_meanGap_before_field"
  err.flush

theorem geometryRow047_meanGap_field :
    geometryRowsJson047.getObjVal? "mean_gap" = .ok (.str geometryRow047_meanGapText) := by rfl

theorem geometryRow047_meanGap_numerator_no_slash :
    geometryRow047_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_meanGap_numerator_parse :
    SourceJson.intChars geometryRow047_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow047_meanGap_denominator_parse :
    SourceJson.intChars geometryRow047_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow047_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_meanGap_parse :
    parseRational geometryRow047_meanGapText = .ok geometryRowsTyped047.meanGap :=
  original_rational_fraction_of_chars geometryRow047_meanGapNumeratorChars geometryRow047_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow047_meanGap_numerator_no_slash geometryRow047_meanGap_numerator_parse
    geometryRow047_meanGap_denominator_parse geometryRow047_meanGap_denominator_nonzero

theorem geometryRow047_meanGap_read :
    rationalField geometryRowsJson047 "mean_gap" = .ok geometryRowsTyped047.meanGap :=
  original_rationalField_of_string geometryRowsJson047 "mean_gap" geometryRow047_meanGapText
    geometryRowsTyped047.meanGap geometryRow047_meanGap_field geometryRow047_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_meanGap_complete"
  err.flush

noncomputable def geometryRow047_jensenBoundNumeratorChars : List Char := ['3', '0', '9', '4', '3', '6', '0', '9', '4', '1', '1', '8', '1', '7', '0', '0', '8', '9', '2', '9', '5', '2', '9', '0', '0', '0', '9', '4', '1', '3', '2', '4', '9', '6', '0', '0', '2', '4', '5', '6', '0', '8', '4', '5', '3', '5', '1', '6', '4', '6', '6', '3', '6', '5', '0', '0', '4', '5', '7', '9', '1', '8', '1', '5', '4', '5', '5', '4', '0', '6', '3', '0', '0', '2', '8', '3', '5', '6', '3', '0', '4', '6', '3', '3', '1', '8', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_jensenBoundDenominatorChars : List Char := ['3', '1', '3', '4', '4', '9', '0', '4', '3', '9', '6', '4', '9', '3', '0', '5', '4', '2', '8', '5', '1', '1', '8', '7', '0', '5', '4', '5', '8', '7', '9', '7', '2', '4', '4', '1', '0', '9', '2', '1', '2', '2', '7', '1', '5', '9', '0', '7', '6', '7', '6', '0', '5', '8', '6', '1', '7', '6', '4', '2', '6', '8', '1', '2', '9', '7', '2', '9', '4', '5', '0', '2', '3', '7', '5', '2', '5', '5', '6', '9', '1', '7', '9', '9', '2', '8', '9', '3', '2', '8', '4', '9', '8', '1', '7', '8', '8', '8', '3', '2', '1', '3', '1', '8', '5', '5', '2', '0', '9', '9', '7', '3', '6', '9', '7', '1', '3', '6', '4', '0', '9', '7', '2', '3', '9', '8', '8', '7']
noncomputable def geometryRow047_jensenBoundText : String := String.ofList (geometryRow047_jensenBoundNumeratorChars ++ '/' :: geometryRow047_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_jensenBound_before_field"
  err.flush

theorem geometryRow047_jensenBound_field :
    geometryRowsJson047.getObjVal? "jensen_bound" = .ok (.str geometryRow047_jensenBoundText) := by rfl

theorem geometryRow047_jensenBound_numerator_no_slash :
    geometryRow047_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow047_jensenBoundNumeratorChars = some (309436094118170089295290009413249600245608453516466365004579181545540630028356304633185280000000000000000000000 : Int) := by decide +kernel

theorem geometryRow047_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow047_jensenBoundDenominatorChars = some (31344904396493054285118705458797244109212271590767605861764268129729450237525569179928932849817888321318552099736971364097239887 : Int) := by decide +kernel

theorem geometryRow047_jensenBound_denominator_nonzero : (31344904396493054285118705458797244109212271590767605861764268129729450237525569179928932849817888321318552099736971364097239887 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_jensenBound_parse :
    parseRational geometryRow047_jensenBoundText = .ok geometryRowsTyped047.jensenBound :=
  original_rational_fraction_of_chars geometryRow047_jensenBoundNumeratorChars geometryRow047_jensenBoundDenominatorChars
    (309436094118170089295290009413249600245608453516466365004579181545540630028356304633185280000000000000000000000 : Int) (31344904396493054285118705458797244109212271590767605861764268129729450237525569179928932849817888321318552099736971364097239887 : Int)
    geometryRow047_jensenBound_numerator_no_slash geometryRow047_jensenBound_numerator_parse
    geometryRow047_jensenBound_denominator_parse geometryRow047_jensenBound_denominator_nonzero

theorem geometryRow047_jensenBound_read :
    rationalField geometryRowsJson047 "jensen_bound" = .ok geometryRowsTyped047.jensenBound :=
  original_rationalField_of_string geometryRowsJson047 "jensen_bound" geometryRow047_jensenBoundText
    geometryRowsTyped047.jensenBound geometryRow047_jensenBound_field geometryRow047_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_factorMaxima_before"
  err.flush

theorem geometryRow047_factorMaxima_read :
    rationalArrayField geometryRowsJson047 "factor_maxima" = .ok geometryRowsTyped047.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_gapWeightedMeans_before"
  err.flush

theorem geometryRow047_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson047 "gap_weighted_means" = .ok geometryRowsTyped047.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow047_floorChars : List Char := ['7', '8', '2', '1', '3', '8', '3', '9', '2', '9', '7', '3']
noncomputable def geometryRow047_floorText : String := String.ofList geometryRow047_floorChars

theorem geometryRow047_floor_text_read :
    geometryRowsJson047.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow047_floorText := by rfl

theorem geometryRow047_floor_chars_parse :
    SourceJson.intChars geometryRow047_floorChars = some (782138392973 : Int) := by decide +kernel

theorem geometryRow047_floor_parse :
    parseInteger geometryRow047_floorText = .ok geometryRowsTyped047.jensenFloorQ96 := by
  simp only [geometryRow047_floorText, parseInteger, String.toList_ofList, geometryRow047_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_047 :
    decodeGeometryRow geometryRowsJson047 = .ok geometryRowsTyped047 :=
  original_geometryRow_of_fields geometryRowsJson047 geometryRowsTyped047 geometryRow047_floorText
    geometryRow047_simplexId_read geometryRow047_vertexIds_read
    geometryRow047_physicalVolume_read geometryRow047_meanGap_read
    geometryRow047_factorMaxima_read geometryRow047_gapWeightedMeans_read
    geometryRow047_jensenBound_read geometryRow047_floor_text_read geometryRow047_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_047_original_decoder_complete"
  err.flush

theorem geometryRow047_shape :
    geometryRowsTyped047.simplexId = 47 ∧
    geometryRowsTyped047.vertexIds.size = 9 ∧ geometryRowsTyped047.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped047.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped047.factorMaxima.size = 10 ∧ geometryRowsTyped047.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock005 : List SourceJson := [geometryRowsJson040, geometryRowsJson041, geometryRowsJson042, geometryRowsJson043, geometryRowsJson044, geometryRowsJson045, geometryRowsJson046, geometryRowsJson047]
noncomputable def geometryRowsTypedBlock005 : List GeometryRow := [geometryRowsTyped040, geometryRowsTyped041, geometryRowsTyped042, geometryRowsTyped043, geometryRowsTyped044, geometryRowsTyped045, geometryRowsTyped046, geometryRowsTyped047]

theorem geometry_Rows_block_005_push_eq (acc : List SourceJson) :
    SimplicesBlock005.blockPush acc = [geometryRowsJson047, geometryRowsJson046, geometryRowsJson045, geometryRowsJson044, geometryRowsJson043, geometryRowsJson042, geometryRowsJson041, geometryRowsJson040] ++ acc := by rfl

theorem geometry_Rows_block_005_reverse (acc : List SourceJson) :
    (SimplicesBlock005.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock005 := by
  rw [geometry_Rows_block_005_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_005 :
    geometryRowsJsonBlock005.mapM decodeGeometryRow = .ok geometryRowsTypedBlock005 := by
  simp only [geometryRowsJsonBlock005, geometryRowsTypedBlock005, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_040, decode_geometry_Rows_041, decode_geometry_Rows_042, decode_geometry_Rows_043, decode_geometry_Rows_044, decode_geometry_Rows_045, decode_geometry_Rows_046, decode_geometry_Rows_047]
  rfl

theorem geometry_Rows_block_005_length : geometryRowsTypedBlock005.length = 8 := by rfl

#print axioms geometryRow040_simplexId_read
#print axioms geometryRow040_vertexIds_read
#print axioms geometryRow040_physicalVolume_field
#print axioms geometryRow040_physicalVolume_numerator_no_slash
#print axioms geometryRow040_physicalVolume_numerator_parse
#print axioms geometryRow040_physicalVolume_denominator_parse
#print axioms geometryRow040_physicalVolume_denominator_nonzero
#print axioms geometryRow040_physicalVolume_parse
#print axioms geometryRow040_physicalVolume_read
#print axioms geometryRow040_meanGap_field
#print axioms geometryRow040_meanGap_numerator_no_slash
#print axioms geometryRow040_meanGap_numerator_parse
#print axioms geometryRow040_meanGap_denominator_parse
#print axioms geometryRow040_meanGap_denominator_nonzero
#print axioms geometryRow040_meanGap_parse
#print axioms geometryRow040_meanGap_read
#print axioms geometryRow040_jensenBound_field
#print axioms geometryRow040_jensenBound_numerator_no_slash
#print axioms geometryRow040_jensenBound_numerator_parse
#print axioms geometryRow040_jensenBound_denominator_parse
#print axioms geometryRow040_jensenBound_denominator_nonzero
#print axioms geometryRow040_jensenBound_parse
#print axioms geometryRow040_jensenBound_read
#print axioms geometryRow040_factorMaxima_read
#print axioms geometryRow040_gapWeightedMeans_read
#print axioms geometryRow040_floor_text_read
#print axioms geometryRow040_floor_chars_parse
#print axioms geometryRow040_floor_parse
#print axioms decode_geometry_Rows_040
#print axioms geometryRow040_shape
#print axioms geometryRow041_simplexId_read
#print axioms geometryRow041_vertexIds_read
#print axioms geometryRow041_physicalVolume_field
#print axioms geometryRow041_physicalVolume_numerator_no_slash
#print axioms geometryRow041_physicalVolume_numerator_parse
#print axioms geometryRow041_physicalVolume_denominator_parse
#print axioms geometryRow041_physicalVolume_denominator_nonzero
#print axioms geometryRow041_physicalVolume_parse
#print axioms geometryRow041_physicalVolume_read
#print axioms geometryRow041_meanGap_field
#print axioms geometryRow041_meanGap_numerator_no_slash
#print axioms geometryRow041_meanGap_numerator_parse
#print axioms geometryRow041_meanGap_denominator_parse
#print axioms geometryRow041_meanGap_denominator_nonzero
#print axioms geometryRow041_meanGap_parse
#print axioms geometryRow041_meanGap_read
#print axioms geometryRow041_jensenBound_field
#print axioms geometryRow041_jensenBound_numerator_no_slash
#print axioms geometryRow041_jensenBound_numerator_parse
#print axioms geometryRow041_jensenBound_denominator_parse
#print axioms geometryRow041_jensenBound_denominator_nonzero
#print axioms geometryRow041_jensenBound_parse
#print axioms geometryRow041_jensenBound_read
#print axioms geometryRow041_factorMaxima_read
#print axioms geometryRow041_gapWeightedMeans_read
#print axioms geometryRow041_floor_text_read
#print axioms geometryRow041_floor_chars_parse
#print axioms geometryRow041_floor_parse
#print axioms decode_geometry_Rows_041
#print axioms geometryRow041_shape
#print axioms geometryRow042_simplexId_read
#print axioms geometryRow042_vertexIds_read
#print axioms geometryRow042_physicalVolume_field
#print axioms geometryRow042_physicalVolume_numerator_no_slash
#print axioms geometryRow042_physicalVolume_numerator_parse
#print axioms geometryRow042_physicalVolume_denominator_parse
#print axioms geometryRow042_physicalVolume_denominator_nonzero
#print axioms geometryRow042_physicalVolume_parse
#print axioms geometryRow042_physicalVolume_read
#print axioms geometryRow042_meanGap_field
#print axioms geometryRow042_meanGap_numerator_no_slash
#print axioms geometryRow042_meanGap_numerator_parse
#print axioms geometryRow042_meanGap_denominator_parse
#print axioms geometryRow042_meanGap_denominator_nonzero
#print axioms geometryRow042_meanGap_parse
#print axioms geometryRow042_meanGap_read
#print axioms geometryRow042_jensenBound_field
#print axioms geometryRow042_jensenBound_numerator_no_slash
#print axioms geometryRow042_jensenBound_numerator_parse
#print axioms geometryRow042_jensenBound_denominator_parse
#print axioms geometryRow042_jensenBound_denominator_nonzero
#print axioms geometryRow042_jensenBound_parse
#print axioms geometryRow042_jensenBound_read
#print axioms geometryRow042_factorMaxima_read
#print axioms geometryRow042_gapWeightedMeans_read
#print axioms geometryRow042_floor_text_read
#print axioms geometryRow042_floor_chars_parse
#print axioms geometryRow042_floor_parse
#print axioms decode_geometry_Rows_042
#print axioms geometryRow042_shape
#print axioms geometryRow043_simplexId_read
#print axioms geometryRow043_vertexIds_read
#print axioms geometryRow043_physicalVolume_field
#print axioms geometryRow043_physicalVolume_numerator_no_slash
#print axioms geometryRow043_physicalVolume_numerator_parse
#print axioms geometryRow043_physicalVolume_denominator_parse
#print axioms geometryRow043_physicalVolume_denominator_nonzero
#print axioms geometryRow043_physicalVolume_parse
#print axioms geometryRow043_physicalVolume_read
#print axioms geometryRow043_meanGap_field
#print axioms geometryRow043_meanGap_numerator_no_slash
#print axioms geometryRow043_meanGap_numerator_parse
#print axioms geometryRow043_meanGap_denominator_parse
#print axioms geometryRow043_meanGap_denominator_nonzero
#print axioms geometryRow043_meanGap_parse
#print axioms geometryRow043_meanGap_read
#print axioms geometryRow043_jensenBound_field
#print axioms geometryRow043_jensenBound_numerator_no_slash
#print axioms geometryRow043_jensenBound_numerator_parse
#print axioms geometryRow043_jensenBound_denominator_parse
#print axioms geometryRow043_jensenBound_denominator_nonzero
#print axioms geometryRow043_jensenBound_parse
#print axioms geometryRow043_jensenBound_read
#print axioms geometryRow043_factorMaxima_read
#print axioms geometryRow043_gapWeightedMeans_read
#print axioms geometryRow043_floor_text_read
#print axioms geometryRow043_floor_chars_parse
#print axioms geometryRow043_floor_parse
#print axioms decode_geometry_Rows_043
#print axioms geometryRow043_shape
#print axioms geometryRow044_simplexId_read
#print axioms geometryRow044_vertexIds_read
#print axioms geometryRow044_physicalVolume_field
#print axioms geometryRow044_physicalVolume_numerator_no_slash
#print axioms geometryRow044_physicalVolume_numerator_parse
#print axioms geometryRow044_physicalVolume_denominator_parse
#print axioms geometryRow044_physicalVolume_denominator_nonzero
#print axioms geometryRow044_physicalVolume_parse
#print axioms geometryRow044_physicalVolume_read
#print axioms geometryRow044_meanGap_field
#print axioms geometryRow044_meanGap_numerator_no_slash
#print axioms geometryRow044_meanGap_numerator_parse
#print axioms geometryRow044_meanGap_denominator_parse
#print axioms geometryRow044_meanGap_denominator_nonzero
#print axioms geometryRow044_meanGap_parse
#print axioms geometryRow044_meanGap_read
#print axioms geometryRow044_jensenBound_field
#print axioms geometryRow044_jensenBound_numerator_no_slash
#print axioms geometryRow044_jensenBound_numerator_parse
#print axioms geometryRow044_jensenBound_denominator_parse
#print axioms geometryRow044_jensenBound_denominator_nonzero
#print axioms geometryRow044_jensenBound_parse
#print axioms geometryRow044_jensenBound_read
#print axioms geometryRow044_factorMaxima_read
#print axioms geometryRow044_gapWeightedMeans_read
#print axioms geometryRow044_floor_text_read
#print axioms geometryRow044_floor_chars_parse
#print axioms geometryRow044_floor_parse
#print axioms decode_geometry_Rows_044
#print axioms geometryRow044_shape
#print axioms geometryRow045_simplexId_read
#print axioms geometryRow045_vertexIds_read
#print axioms geometryRow045_physicalVolume_field
#print axioms geometryRow045_physicalVolume_numerator_no_slash
#print axioms geometryRow045_physicalVolume_numerator_parse
#print axioms geometryRow045_physicalVolume_denominator_parse
#print axioms geometryRow045_physicalVolume_denominator_nonzero
#print axioms geometryRow045_physicalVolume_parse
#print axioms geometryRow045_physicalVolume_read
#print axioms geometryRow045_meanGap_field
#print axioms geometryRow045_meanGap_numerator_no_slash
#print axioms geometryRow045_meanGap_numerator_parse
#print axioms geometryRow045_meanGap_denominator_parse
#print axioms geometryRow045_meanGap_denominator_nonzero
#print axioms geometryRow045_meanGap_parse
#print axioms geometryRow045_meanGap_read
#print axioms geometryRow045_jensenBound_field
#print axioms geometryRow045_jensenBound_numerator_no_slash
#print axioms geometryRow045_jensenBound_numerator_parse
#print axioms geometryRow045_jensenBound_denominator_parse
#print axioms geometryRow045_jensenBound_denominator_nonzero
#print axioms geometryRow045_jensenBound_parse
#print axioms geometryRow045_jensenBound_read
#print axioms geometryRow045_factorMaxima_read
#print axioms geometryRow045_gapWeightedMeans_read
#print axioms geometryRow045_floor_text_read
#print axioms geometryRow045_floor_chars_parse
#print axioms geometryRow045_floor_parse
#print axioms decode_geometry_Rows_045
#print axioms geometryRow045_shape
#print axioms geometryRow046_simplexId_read
#print axioms geometryRow046_vertexIds_read
#print axioms geometryRow046_physicalVolume_field
#print axioms geometryRow046_physicalVolume_numerator_no_slash
#print axioms geometryRow046_physicalVolume_numerator_parse
#print axioms geometryRow046_physicalVolume_denominator_parse
#print axioms geometryRow046_physicalVolume_denominator_nonzero
#print axioms geometryRow046_physicalVolume_parse
#print axioms geometryRow046_physicalVolume_read
#print axioms geometryRow046_meanGap_field
#print axioms geometryRow046_meanGap_numerator_no_slash
#print axioms geometryRow046_meanGap_numerator_parse
#print axioms geometryRow046_meanGap_denominator_parse
#print axioms geometryRow046_meanGap_denominator_nonzero
#print axioms geometryRow046_meanGap_parse
#print axioms geometryRow046_meanGap_read
#print axioms geometryRow046_jensenBound_field
#print axioms geometryRow046_jensenBound_numerator_no_slash
#print axioms geometryRow046_jensenBound_numerator_parse
#print axioms geometryRow046_jensenBound_denominator_parse
#print axioms geometryRow046_jensenBound_denominator_nonzero
#print axioms geometryRow046_jensenBound_parse
#print axioms geometryRow046_jensenBound_read
#print axioms geometryRow046_factorMaxima_read
#print axioms geometryRow046_gapWeightedMeans_read
#print axioms geometryRow046_floor_text_read
#print axioms geometryRow046_floor_chars_parse
#print axioms geometryRow046_floor_parse
#print axioms decode_geometry_Rows_046
#print axioms geometryRow046_shape
#print axioms geometryRow047_simplexId_read
#print axioms geometryRow047_vertexIds_read
#print axioms geometryRow047_physicalVolume_field
#print axioms geometryRow047_physicalVolume_numerator_no_slash
#print axioms geometryRow047_physicalVolume_numerator_parse
#print axioms geometryRow047_physicalVolume_denominator_parse
#print axioms geometryRow047_physicalVolume_denominator_nonzero
#print axioms geometryRow047_physicalVolume_parse
#print axioms geometryRow047_physicalVolume_read
#print axioms geometryRow047_meanGap_field
#print axioms geometryRow047_meanGap_numerator_no_slash
#print axioms geometryRow047_meanGap_numerator_parse
#print axioms geometryRow047_meanGap_denominator_parse
#print axioms geometryRow047_meanGap_denominator_nonzero
#print axioms geometryRow047_meanGap_parse
#print axioms geometryRow047_meanGap_read
#print axioms geometryRow047_jensenBound_field
#print axioms geometryRow047_jensenBound_numerator_no_slash
#print axioms geometryRow047_jensenBound_numerator_parse
#print axioms geometryRow047_jensenBound_denominator_parse
#print axioms geometryRow047_jensenBound_denominator_nonzero
#print axioms geometryRow047_jensenBound_parse
#print axioms geometryRow047_jensenBound_read
#print axioms geometryRow047_factorMaxima_read
#print axioms geometryRow047_gapWeightedMeans_read
#print axioms geometryRow047_floor_text_read
#print axioms geometryRow047_floor_chars_parse
#print axioms geometryRow047_floor_parse
#print axioms decode_geometry_Rows_047
#print axioms geometryRow047_shape
#print axioms geometry_Rows_block_005_push_eq
#print axioms geometry_Rows_block_005_reverse
#print axioms decode_geometry_Rows_block_005
#print axioms geometry_Rows_block_005_length

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
