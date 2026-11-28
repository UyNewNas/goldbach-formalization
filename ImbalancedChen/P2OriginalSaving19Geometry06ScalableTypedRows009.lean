import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock009

/-! Local typed certificates for original cell 06, rows 72 through 79.
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

noncomputable def geometryRowsJson072 : SourceJson :=
  (SimplicesBlock009.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped072 : GeometryRow :=
  { simplexId := 72,
    vertexIds := #[32, 30, 28, 26, 23, 13, 10, 1, 0],
    physicalVolume := ((2170330984689014173546686240191215633 : ℚ) / (326666001664800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((275312173209776114597 : ℚ) / (3199182368243400000000 : ℚ)), ((40242048716552682173 : ℚ) / (457026052606200000000 : ℚ)), ((827236203753219721 : ℚ) / (6954744278790000000 : ℚ)), ((99059936396744249557 : ℚ) / (1066394122747800000000 : ℚ)), ((32826814125151936279 : ℚ) / (355464707582600000000 : ℚ)), ((10450502879250812711 : ℚ) / (145417380374700000000 : ℚ)), ((11095673807894758241 : ℚ) / (290834760749400000000 : ℚ)), ((9545688525484124261 : ℚ) / (290834760749400000000 : ℚ)), ((9387586534544217821 : ℚ) / (290834760749400000000 : ℚ)), ((13731368359024304431 : ℚ) / (457026052606200000000 : ℚ))],
    jensenBound := ((247481198098353043076719979137142454917208428952154479255123448366843812612301814869113073055685716693208856310097557578012953686416808881772109218529809280000000000000000000000 : ℚ) / (4252337352513104551505506273551895783877933763118705352585980506049737553331900838442001065555417414810314071723162333893985643425988698555779885278996479969919537843096060673867200101573912083 : ℚ)),
    jensenFloorQ96 := (4610988958948 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_simplexId_before"
  err.flush

theorem geometryRow072_simplexId_read :
    geometryRowsJson072.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped072.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_vertexIds_before"
  err.flush

theorem geometryRow072_vertexIds_read :
    geometryRowsJson072.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped072.vertexIds := by decide +kernel

noncomputable def geometryRow072_physicalVolumeNumeratorChars : List Char := ['2', '1', '7', '0', '3', '3', '0', '9', '8', '4', '6', '8', '9', '0', '1', '4', '1', '7', '3', '5', '4', '6', '6', '8', '6', '2', '4', '0', '1', '9', '1', '2', '1', '5', '6', '3', '3']
noncomputable def geometryRow072_physicalVolumeDenominatorChars : List Char := ['3', '2', '6', '6', '6', '6', '0', '0', '1', '6', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow072_physicalVolumeText : String := String.ofList (geometryRow072_physicalVolumeNumeratorChars ++ '/' :: geometryRow072_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_physicalVolume_before_field"
  err.flush

theorem geometryRow072_physicalVolume_field :
    geometryRowsJson072.getObjVal? "physical_volume" = .ok (.str geometryRow072_physicalVolumeText) := by rfl

theorem geometryRow072_physicalVolume_numerator_no_slash :
    geometryRow072_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow072_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow072_physicalVolumeNumeratorChars = some (2170330984689014173546686240191215633 : Int) := by decide +kernel

theorem geometryRow072_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow072_physicalVolumeDenominatorChars = some (326666001664800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow072_physicalVolume_denominator_nonzero : (326666001664800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow072_physicalVolume_parse :
    parseRational geometryRow072_physicalVolumeText = .ok geometryRowsTyped072.physicalVolume :=
  original_rational_fraction_of_chars geometryRow072_physicalVolumeNumeratorChars geometryRow072_physicalVolumeDenominatorChars
    (2170330984689014173546686240191215633 : Int) (326666001664800000000000000000000000000000000000000000000000000 : Int)
    geometryRow072_physicalVolume_numerator_no_slash geometryRow072_physicalVolume_numerator_parse
    geometryRow072_physicalVolume_denominator_parse geometryRow072_physicalVolume_denominator_nonzero

theorem geometryRow072_physicalVolume_read :
    rationalField geometryRowsJson072 "physical_volume" = .ok geometryRowsTyped072.physicalVolume :=
  original_rationalField_of_string geometryRowsJson072 "physical_volume" geometryRow072_physicalVolumeText
    geometryRowsTyped072.physicalVolume geometryRow072_physicalVolume_field geometryRow072_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_physicalVolume_complete"
  err.flush

noncomputable def geometryRow072_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow072_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow072_meanGapText : String := String.ofList (geometryRow072_meanGapNumeratorChars ++ '/' :: geometryRow072_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_meanGap_before_field"
  err.flush

theorem geometryRow072_meanGap_field :
    geometryRowsJson072.getObjVal? "mean_gap" = .ok (.str geometryRow072_meanGapText) := by rfl

theorem geometryRow072_meanGap_numerator_no_slash :
    geometryRow072_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow072_meanGap_numerator_parse :
    SourceJson.intChars geometryRow072_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow072_meanGap_denominator_parse :
    SourceJson.intChars geometryRow072_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow072_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow072_meanGap_parse :
    parseRational geometryRow072_meanGapText = .ok geometryRowsTyped072.meanGap :=
  original_rational_fraction_of_chars geometryRow072_meanGapNumeratorChars geometryRow072_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow072_meanGap_numerator_no_slash geometryRow072_meanGap_numerator_parse
    geometryRow072_meanGap_denominator_parse geometryRow072_meanGap_denominator_nonzero

theorem geometryRow072_meanGap_read :
    rationalField geometryRowsJson072 "mean_gap" = .ok geometryRowsTyped072.meanGap :=
  original_rationalField_of_string geometryRowsJson072 "mean_gap" geometryRow072_meanGapText
    geometryRowsTyped072.meanGap geometryRow072_meanGap_field geometryRow072_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_meanGap_complete"
  err.flush

noncomputable def geometryRow072_jensenBoundNumeratorChars : List Char := ['2', '4', '7', '4', '8', '1', '1', '9', '8', '0', '9', '8', '3', '5', '3', '0', '4', '3', '0', '7', '6', '7', '1', '9', '9', '7', '9', '1', '3', '7', '1', '4', '2', '4', '5', '4', '9', '1', '7', '2', '0', '8', '4', '2', '8', '9', '5', '2', '1', '5', '4', '4', '7', '9', '2', '5', '5', '1', '2', '3', '4', '4', '8', '3', '6', '6', '8', '4', '3', '8', '1', '2', '6', '1', '2', '3', '0', '1', '8', '1', '4', '8', '6', '9', '1', '1', '3', '0', '7', '3', '0', '5', '5', '6', '8', '5', '7', '1', '6', '6', '9', '3', '2', '0', '8', '8', '5', '6', '3', '1', '0', '0', '9', '7', '5', '5', '7', '5', '7', '8', '0', '1', '2', '9', '5', '3', '6', '8', '6', '4', '1', '6', '8', '0', '8', '8', '8', '1', '7', '7', '2', '1', '0', '9', '2', '1', '8', '5', '2', '9', '8', '0', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow072_jensenBoundDenominatorChars : List Char := ['4', '2', '5', '2', '3', '3', '7', '3', '5', '2', '5', '1', '3', '1', '0', '4', '5', '5', '1', '5', '0', '5', '5', '0', '6', '2', '7', '3', '5', '5', '1', '8', '9', '5', '7', '8', '3', '8', '7', '7', '9', '3', '3', '7', '6', '3', '1', '1', '8', '7', '0', '5', '3', '5', '2', '5', '8', '5', '9', '8', '0', '5', '0', '6', '0', '4', '9', '7', '3', '7', '5', '5', '3', '3', '3', '1', '9', '0', '0', '8', '3', '8', '4', '4', '2', '0', '0', '1', '0', '6', '5', '5', '5', '5', '4', '1', '7', '4', '1', '4', '8', '1', '0', '3', '1', '4', '0', '7', '1', '7', '2', '3', '1', '6', '2', '3', '3', '3', '8', '9', '3', '9', '8', '5', '6', '4', '3', '4', '2', '5', '9', '8', '8', '6', '9', '8', '5', '5', '5', '7', '7', '9', '8', '8', '5', '2', '7', '8', '9', '9', '6', '4', '7', '9', '9', '6', '9', '9', '1', '9', '5', '3', '7', '8', '4', '3', '0', '9', '6', '0', '6', '0', '6', '7', '3', '8', '6', '7', '2', '0', '0', '1', '0', '1', '5', '7', '3', '9', '1', '2', '0', '8', '3']
noncomputable def geometryRow072_jensenBoundText : String := String.ofList (geometryRow072_jensenBoundNumeratorChars ++ '/' :: geometryRow072_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_jensenBound_before_field"
  err.flush

theorem geometryRow072_jensenBound_field :
    geometryRowsJson072.getObjVal? "jensen_bound" = .ok (.str geometryRow072_jensenBoundText) := by rfl

theorem geometryRow072_jensenBound_numerator_no_slash :
    geometryRow072_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow072_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow072_jensenBoundNumeratorChars = some (247481198098353043076719979137142454917208428952154479255123448366843812612301814869113073055685716693208856310097557578012953686416808881772109218529809280000000000000000000000 : Int) := by decide +kernel

theorem geometryRow072_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow072_jensenBoundDenominatorChars = some (4252337352513104551505506273551895783877933763118705352585980506049737553331900838442001065555417414810314071723162333893985643425988698555779885278996479969919537843096060673867200101573912083 : Int) := by decide +kernel

theorem geometryRow072_jensenBound_denominator_nonzero : (4252337352513104551505506273551895783877933763118705352585980506049737553331900838442001065555417414810314071723162333893985643425988698555779885278996479969919537843096060673867200101573912083 : Int) ≠ 0 := by decide +kernel

theorem geometryRow072_jensenBound_parse :
    parseRational geometryRow072_jensenBoundText = .ok geometryRowsTyped072.jensenBound :=
  original_rational_fraction_of_chars geometryRow072_jensenBoundNumeratorChars geometryRow072_jensenBoundDenominatorChars
    (247481198098353043076719979137142454917208428952154479255123448366843812612301814869113073055685716693208856310097557578012953686416808881772109218529809280000000000000000000000 : Int) (4252337352513104551505506273551895783877933763118705352585980506049737553331900838442001065555417414810314071723162333893985643425988698555779885278996479969919537843096060673867200101573912083 : Int)
    geometryRow072_jensenBound_numerator_no_slash geometryRow072_jensenBound_numerator_parse
    geometryRow072_jensenBound_denominator_parse geometryRow072_jensenBound_denominator_nonzero

theorem geometryRow072_jensenBound_read :
    rationalField geometryRowsJson072 "jensen_bound" = .ok geometryRowsTyped072.jensenBound :=
  original_rationalField_of_string geometryRowsJson072 "jensen_bound" geometryRow072_jensenBoundText
    geometryRowsTyped072.jensenBound geometryRow072_jensenBound_field geometryRow072_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_factorMaxima_before"
  err.flush

theorem geometryRow072_factorMaxima_read :
    rationalArrayField geometryRowsJson072 "factor_maxima" = .ok geometryRowsTyped072.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_gapWeightedMeans_before"
  err.flush

theorem geometryRow072_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson072 "gap_weighted_means" = .ok geometryRowsTyped072.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow072_floorChars : List Char := ['4', '6', '1', '0', '9', '8', '8', '9', '5', '8', '9', '4', '8']
noncomputable def geometryRow072_floorText : String := String.ofList geometryRow072_floorChars

theorem geometryRow072_floor_text_read :
    geometryRowsJson072.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow072_floorText := by rfl

theorem geometryRow072_floor_chars_parse :
    SourceJson.intChars geometryRow072_floorChars = some (4610988958948 : Int) := by decide +kernel

theorem geometryRow072_floor_parse :
    parseInteger geometryRow072_floorText = .ok geometryRowsTyped072.jensenFloorQ96 := by
  simp only [geometryRow072_floorText, parseInteger, String.toList_ofList, geometryRow072_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_072 :
    decodeGeometryRow geometryRowsJson072 = .ok geometryRowsTyped072 :=
  original_geometryRow_of_fields geometryRowsJson072 geometryRowsTyped072 geometryRow072_floorText
    geometryRow072_simplexId_read geometryRow072_vertexIds_read
    geometryRow072_physicalVolume_read geometryRow072_meanGap_read
    geometryRow072_factorMaxima_read geometryRow072_gapWeightedMeans_read
    geometryRow072_jensenBound_read geometryRow072_floor_text_read geometryRow072_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_072_original_decoder_complete"
  err.flush

theorem geometryRow072_shape :
    geometryRowsTyped072.simplexId = 72 ∧
    geometryRowsTyped072.vertexIds.size = 9 ∧ geometryRowsTyped072.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped072.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped072.factorMaxima.size = 10 ∧ geometryRowsTyped072.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson073 : SourceJson :=
  (SimplicesBlock009.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped073 : GeometryRow :=
  { simplexId := 73,
    vertexIds := #[32, 30, 28, 26, 23, 13, 10, 8, 0],
    physicalVolume := ((48026896221518747767521232067268044413 : ℚ) / (719998534281600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((272126012509 : ℚ) / (3187800000000 : ℚ)), ((276336461647 : ℚ) / (3187800000000 : ℚ)), ((9909952321 : ℚ) / (83160000000 : ℚ)), ((55121824601 : ℚ) / (597712500000 : ℚ)), ((27398509483 : ℚ) / (298856250000 : ℚ)), ((63459368617 : ℚ) / (869400000000 : ℚ)), ((33548843261 : ℚ) / (869400000000 : ℚ)), ((1040513087 : ℚ) / (31050000000 : ℚ)), ((1023633857 : ℚ) / (31050000000 : ℚ)), ((282977144927 : ℚ) / (9563400000000 : ℚ))],
    jensenBound := ((349694301481672893596102575792032003447358006926243026060358336309843750000000000000000 : ℚ) / (1226116930439058364631835956735007681349645265204528024256141321575655481843177920048167107578848849441 : ℚ)),
    jensenFloorQ96 := (22596243686302 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_simplexId_before"
  err.flush

theorem geometryRow073_simplexId_read :
    geometryRowsJson073.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped073.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_vertexIds_before"
  err.flush

theorem geometryRow073_vertexIds_read :
    geometryRowsJson073.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped073.vertexIds := by decide +kernel

noncomputable def geometryRow073_physicalVolumeNumeratorChars : List Char := ['4', '8', '0', '2', '6', '8', '9', '6', '2', '2', '1', '5', '1', '8', '7', '4', '7', '7', '6', '7', '5', '2', '1', '2', '3', '2', '0', '6', '7', '2', '6', '8', '0', '4', '4', '4', '1', '3']
noncomputable def geometryRow073_physicalVolumeDenominatorChars : List Char := ['7', '1', '9', '9', '9', '8', '5', '3', '4', '2', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow073_physicalVolumeText : String := String.ofList (geometryRow073_physicalVolumeNumeratorChars ++ '/' :: geometryRow073_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_physicalVolume_before_field"
  err.flush

theorem geometryRow073_physicalVolume_field :
    geometryRowsJson073.getObjVal? "physical_volume" = .ok (.str geometryRow073_physicalVolumeText) := by rfl

theorem geometryRow073_physicalVolume_numerator_no_slash :
    geometryRow073_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow073_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow073_physicalVolumeNumeratorChars = some (48026896221518747767521232067268044413 : Int) := by decide +kernel

theorem geometryRow073_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow073_physicalVolumeDenominatorChars = some (719998534281600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow073_physicalVolume_denominator_nonzero : (719998534281600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow073_physicalVolume_parse :
    parseRational geometryRow073_physicalVolumeText = .ok geometryRowsTyped073.physicalVolume :=
  original_rational_fraction_of_chars geometryRow073_physicalVolumeNumeratorChars geometryRow073_physicalVolumeDenominatorChars
    (48026896221518747767521232067268044413 : Int) (719998534281600000000000000000000000000000000000000000000000000 : Int)
    geometryRow073_physicalVolume_numerator_no_slash geometryRow073_physicalVolume_numerator_parse
    geometryRow073_physicalVolume_denominator_parse geometryRow073_physicalVolume_denominator_nonzero

theorem geometryRow073_physicalVolume_read :
    rationalField geometryRowsJson073 "physical_volume" = .ok geometryRowsTyped073.physicalVolume :=
  original_rationalField_of_string geometryRowsJson073 "physical_volume" geometryRow073_physicalVolumeText
    geometryRowsTyped073.physicalVolume geometryRow073_physicalVolume_field geometryRow073_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_physicalVolume_complete"
  err.flush

noncomputable def geometryRow073_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow073_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow073_meanGapText : String := String.ofList (geometryRow073_meanGapNumeratorChars ++ '/' :: geometryRow073_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_meanGap_before_field"
  err.flush

theorem geometryRow073_meanGap_field :
    geometryRowsJson073.getObjVal? "mean_gap" = .ok (.str geometryRow073_meanGapText) := by rfl

theorem geometryRow073_meanGap_numerator_no_slash :
    geometryRow073_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow073_meanGap_numerator_parse :
    SourceJson.intChars geometryRow073_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow073_meanGap_denominator_parse :
    SourceJson.intChars geometryRow073_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow073_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow073_meanGap_parse :
    parseRational geometryRow073_meanGapText = .ok geometryRowsTyped073.meanGap :=
  original_rational_fraction_of_chars geometryRow073_meanGapNumeratorChars geometryRow073_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow073_meanGap_numerator_no_slash geometryRow073_meanGap_numerator_parse
    geometryRow073_meanGap_denominator_parse geometryRow073_meanGap_denominator_nonzero

theorem geometryRow073_meanGap_read :
    rationalField geometryRowsJson073 "mean_gap" = .ok geometryRowsTyped073.meanGap :=
  original_rationalField_of_string geometryRowsJson073 "mean_gap" geometryRow073_meanGapText
    geometryRowsTyped073.meanGap geometryRow073_meanGap_field geometryRow073_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_meanGap_complete"
  err.flush

noncomputable def geometryRow073_jensenBoundNumeratorChars : List Char := ['3', '4', '9', '6', '9', '4', '3', '0', '1', '4', '8', '1', '6', '7', '2', '8', '9', '3', '5', '9', '6', '1', '0', '2', '5', '7', '5', '7', '9', '2', '0', '3', '2', '0', '0', '3', '4', '4', '7', '3', '5', '8', '0', '0', '6', '9', '2', '6', '2', '4', '3', '0', '2', '6', '0', '6', '0', '3', '5', '8', '3', '3', '6', '3', '0', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow073_jensenBoundDenominatorChars : List Char := ['1', '2', '2', '6', '1', '1', '6', '9', '3', '0', '4', '3', '9', '0', '5', '8', '3', '6', '4', '6', '3', '1', '8', '3', '5', '9', '5', '6', '7', '3', '5', '0', '0', '7', '6', '8', '1', '3', '4', '9', '6', '4', '5', '2', '6', '5', '2', '0', '4', '5', '2', '8', '0', '2', '4', '2', '5', '6', '1', '4', '1', '3', '2', '1', '5', '7', '5', '6', '5', '5', '4', '8', '1', '8', '4', '3', '1', '7', '7', '9', '2', '0', '0', '4', '8', '1', '6', '7', '1', '0', '7', '5', '7', '8', '8', '4', '8', '8', '4', '9', '4', '4', '1']
noncomputable def geometryRow073_jensenBoundText : String := String.ofList (geometryRow073_jensenBoundNumeratorChars ++ '/' :: geometryRow073_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_jensenBound_before_field"
  err.flush

theorem geometryRow073_jensenBound_field :
    geometryRowsJson073.getObjVal? "jensen_bound" = .ok (.str geometryRow073_jensenBoundText) := by rfl

theorem geometryRow073_jensenBound_numerator_no_slash :
    geometryRow073_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow073_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow073_jensenBoundNumeratorChars = some (349694301481672893596102575792032003447358006926243026060358336309843750000000000000000 : Int) := by decide +kernel

theorem geometryRow073_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow073_jensenBoundDenominatorChars = some (1226116930439058364631835956735007681349645265204528024256141321575655481843177920048167107578848849441 : Int) := by decide +kernel

theorem geometryRow073_jensenBound_denominator_nonzero : (1226116930439058364631835956735007681349645265204528024256141321575655481843177920048167107578848849441 : Int) ≠ 0 := by decide +kernel

theorem geometryRow073_jensenBound_parse :
    parseRational geometryRow073_jensenBoundText = .ok geometryRowsTyped073.jensenBound :=
  original_rational_fraction_of_chars geometryRow073_jensenBoundNumeratorChars geometryRow073_jensenBoundDenominatorChars
    (349694301481672893596102575792032003447358006926243026060358336309843750000000000000000 : Int) (1226116930439058364631835956735007681349645265204528024256141321575655481843177920048167107578848849441 : Int)
    geometryRow073_jensenBound_numerator_no_slash geometryRow073_jensenBound_numerator_parse
    geometryRow073_jensenBound_denominator_parse geometryRow073_jensenBound_denominator_nonzero

theorem geometryRow073_jensenBound_read :
    rationalField geometryRowsJson073 "jensen_bound" = .ok geometryRowsTyped073.jensenBound :=
  original_rationalField_of_string geometryRowsJson073 "jensen_bound" geometryRow073_jensenBoundText
    geometryRowsTyped073.jensenBound geometryRow073_jensenBound_field geometryRow073_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_factorMaxima_before"
  err.flush

theorem geometryRow073_factorMaxima_read :
    rationalArrayField geometryRowsJson073 "factor_maxima" = .ok geometryRowsTyped073.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_gapWeightedMeans_before"
  err.flush

theorem geometryRow073_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson073 "gap_weighted_means" = .ok geometryRowsTyped073.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow073_floorChars : List Char := ['2', '2', '5', '9', '6', '2', '4', '3', '6', '8', '6', '3', '0', '2']
noncomputable def geometryRow073_floorText : String := String.ofList geometryRow073_floorChars

theorem geometryRow073_floor_text_read :
    geometryRowsJson073.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow073_floorText := by rfl

theorem geometryRow073_floor_chars_parse :
    SourceJson.intChars geometryRow073_floorChars = some (22596243686302 : Int) := by decide +kernel

theorem geometryRow073_floor_parse :
    parseInteger geometryRow073_floorText = .ok geometryRowsTyped073.jensenFloorQ96 := by
  simp only [geometryRow073_floorText, parseInteger, String.toList_ofList, geometryRow073_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_073 :
    decodeGeometryRow geometryRowsJson073 = .ok geometryRowsTyped073 :=
  original_geometryRow_of_fields geometryRowsJson073 geometryRowsTyped073 geometryRow073_floorText
    geometryRow073_simplexId_read geometryRow073_vertexIds_read
    geometryRow073_physicalVolume_read geometryRow073_meanGap_read
    geometryRow073_factorMaxima_read geometryRow073_gapWeightedMeans_read
    geometryRow073_jensenBound_read geometryRow073_floor_text_read geometryRow073_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_073_original_decoder_complete"
  err.flush

theorem geometryRow073_shape :
    geometryRowsTyped073.simplexId = 73 ∧
    geometryRowsTyped073.vertexIds.size = 9 ∧ geometryRowsTyped073.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped073.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped073.factorMaxima.size = 10 ∧ geometryRowsTyped073.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson074 : SourceJson :=
  (SimplicesBlock009.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped074 : GeometryRow :=
  { simplexId := 74,
    vertexIds := #[32, 30, 28, 26, 23, 22, 13, 4, 0],
    physicalVolume := ((50734102723982295638241231086055793 : ℚ) / (11944420128900000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((96707389 : ℚ) / (66220000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((765619 : ℚ) / (10062500 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((282095461036165220977 : ℚ) / (3314051007532650000000 : ℚ)), ((13424617550025177019 : ℚ) / (154141907327100000000 : ℚ)), ((768503321801566539 : ℚ) / (6403963299580000000 : ℚ)), ((7434851016237748613 : ℚ) / (78905976369825000000 : ℚ)), ((2463990788371170261 : ℚ) / (26301992123275000000 : ℚ)), ((14129073505741335823 : ℚ) / (200851576214100000000 : ℚ)), ((7288680177764043739 : ℚ) / (200851576214100000000 : ℚ)), ((832635325636764463 : ℚ) / (25106447026762500000 : ℚ)), ((1637974194342930511 : ℚ) / (50212894053525000000 : ℚ)), ((4581906373539184993 : ℚ) / (154141907327100000000 : ℚ))],
    jensenBound := ((3535431332395132006584021142566447085839502561840323163116513059790899404233877474579601686282511873927694459990036426381508637921368874958679884726562500000000000000 : ℚ) / (91855210519539078772007358433556088501972451628862171539520447209658452581966190868593397271071315503244389713639871666538929088029629750899333374529970577236932512550583653853732339 : ℚ)),
    jensenFloorQ96 := (3049426663732 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_simplexId_before"
  err.flush

theorem geometryRow074_simplexId_read :
    geometryRowsJson074.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped074.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_vertexIds_before"
  err.flush

theorem geometryRow074_vertexIds_read :
    geometryRowsJson074.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped074.vertexIds := by decide +kernel

noncomputable def geometryRow074_physicalVolumeNumeratorChars : List Char := ['5', '0', '7', '3', '4', '1', '0', '2', '7', '2', '3', '9', '8', '2', '2', '9', '5', '6', '3', '8', '2', '4', '1', '2', '3', '1', '0', '8', '6', '0', '5', '5', '7', '9', '3']
noncomputable def geometryRow074_physicalVolumeDenominatorChars : List Char := ['1', '1', '9', '4', '4', '4', '2', '0', '1', '2', '8', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow074_physicalVolumeText : String := String.ofList (geometryRow074_physicalVolumeNumeratorChars ++ '/' :: geometryRow074_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_physicalVolume_before_field"
  err.flush

theorem geometryRow074_physicalVolume_field :
    geometryRowsJson074.getObjVal? "physical_volume" = .ok (.str geometryRow074_physicalVolumeText) := by rfl

theorem geometryRow074_physicalVolume_numerator_no_slash :
    geometryRow074_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow074_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow074_physicalVolumeNumeratorChars = some (50734102723982295638241231086055793 : Int) := by decide +kernel

theorem geometryRow074_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow074_physicalVolumeDenominatorChars = some (11944420128900000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow074_physicalVolume_denominator_nonzero : (11944420128900000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow074_physicalVolume_parse :
    parseRational geometryRow074_physicalVolumeText = .ok geometryRowsTyped074.physicalVolume :=
  original_rational_fraction_of_chars geometryRow074_physicalVolumeNumeratorChars geometryRow074_physicalVolumeDenominatorChars
    (50734102723982295638241231086055793 : Int) (11944420128900000000000000000000000000000000000000000000000000 : Int)
    geometryRow074_physicalVolume_numerator_no_slash geometryRow074_physicalVolume_numerator_parse
    geometryRow074_physicalVolume_denominator_parse geometryRow074_physicalVolume_denominator_nonzero

theorem geometryRow074_physicalVolume_read :
    rationalField geometryRowsJson074 "physical_volume" = .ok geometryRowsTyped074.physicalVolume :=
  original_rationalField_of_string geometryRowsJson074 "physical_volume" geometryRow074_physicalVolumeText
    geometryRowsTyped074.physicalVolume geometryRow074_physicalVolume_field geometryRow074_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_physicalVolume_complete"
  err.flush

noncomputable def geometryRow074_meanGapNumeratorChars : List Char := ['9', '6', '7', '0', '7', '3', '8', '9']
noncomputable def geometryRow074_meanGapDenominatorChars : List Char := ['6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow074_meanGapText : String := String.ofList (geometryRow074_meanGapNumeratorChars ++ '/' :: geometryRow074_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_meanGap_before_field"
  err.flush

theorem geometryRow074_meanGap_field :
    geometryRowsJson074.getObjVal? "mean_gap" = .ok (.str geometryRow074_meanGapText) := by rfl

theorem geometryRow074_meanGap_numerator_no_slash :
    geometryRow074_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow074_meanGap_numerator_parse :
    SourceJson.intChars geometryRow074_meanGapNumeratorChars = some (96707389 : Int) := by decide +kernel

theorem geometryRow074_meanGap_denominator_parse :
    SourceJson.intChars geometryRow074_meanGapDenominatorChars = some (66220000000 : Int) := by decide +kernel

theorem geometryRow074_meanGap_denominator_nonzero : (66220000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow074_meanGap_parse :
    parseRational geometryRow074_meanGapText = .ok geometryRowsTyped074.meanGap :=
  original_rational_fraction_of_chars geometryRow074_meanGapNumeratorChars geometryRow074_meanGapDenominatorChars
    (96707389 : Int) (66220000000 : Int)
    geometryRow074_meanGap_numerator_no_slash geometryRow074_meanGap_numerator_parse
    geometryRow074_meanGap_denominator_parse geometryRow074_meanGap_denominator_nonzero

theorem geometryRow074_meanGap_read :
    rationalField geometryRowsJson074 "mean_gap" = .ok geometryRowsTyped074.meanGap :=
  original_rationalField_of_string geometryRowsJson074 "mean_gap" geometryRow074_meanGapText
    geometryRowsTyped074.meanGap geometryRow074_meanGap_field geometryRow074_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_meanGap_complete"
  err.flush

noncomputable def geometryRow074_jensenBoundNumeratorChars : List Char := ['3', '5', '3', '5', '4', '3', '1', '3', '3', '2', '3', '9', '5', '1', '3', '2', '0', '0', '6', '5', '8', '4', '0', '2', '1', '1', '4', '2', '5', '6', '6', '4', '4', '7', '0', '8', '5', '8', '3', '9', '5', '0', '2', '5', '6', '1', '8', '4', '0', '3', '2', '3', '1', '6', '3', '1', '1', '6', '5', '1', '3', '0', '5', '9', '7', '9', '0', '8', '9', '9', '4', '0', '4', '2', '3', '3', '8', '7', '7', '4', '7', '4', '5', '7', '9', '6', '0', '1', '6', '8', '6', '2', '8', '2', '5', '1', '1', '8', '7', '3', '9', '2', '7', '6', '9', '4', '4', '5', '9', '9', '9', '0', '0', '3', '6', '4', '2', '6', '3', '8', '1', '5', '0', '8', '6', '3', '7', '9', '2', '1', '3', '6', '8', '8', '7', '4', '9', '5', '8', '6', '7', '9', '8', '8', '4', '7', '2', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow074_jensenBoundDenominatorChars : List Char := ['9', '1', '8', '5', '5', '2', '1', '0', '5', '1', '9', '5', '3', '9', '0', '7', '8', '7', '7', '2', '0', '0', '7', '3', '5', '8', '4', '3', '3', '5', '5', '6', '0', '8', '8', '5', '0', '1', '9', '7', '2', '4', '5', '1', '6', '2', '8', '8', '6', '2', '1', '7', '1', '5', '3', '9', '5', '2', '0', '4', '4', '7', '2', '0', '9', '6', '5', '8', '4', '5', '2', '5', '8', '1', '9', '6', '6', '1', '9', '0', '8', '6', '8', '5', '9', '3', '3', '9', '7', '2', '7', '1', '0', '7', '1', '3', '1', '5', '5', '0', '3', '2', '4', '4', '3', '8', '9', '7', '1', '3', '6', '3', '9', '8', '7', '1', '6', '6', '6', '5', '3', '8', '9', '2', '9', '0', '8', '8', '0', '2', '9', '6', '2', '9', '7', '5', '0', '8', '9', '9', '3', '3', '3', '3', '7', '4', '5', '2', '9', '9', '7', '0', '5', '7', '7', '2', '3', '6', '9', '3', '2', '5', '1', '2', '5', '5', '0', '5', '8', '3', '6', '5', '3', '8', '5', '3', '7', '3', '2', '3', '3', '9']
noncomputable def geometryRow074_jensenBoundText : String := String.ofList (geometryRow074_jensenBoundNumeratorChars ++ '/' :: geometryRow074_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_jensenBound_before_field"
  err.flush

theorem geometryRow074_jensenBound_field :
    geometryRowsJson074.getObjVal? "jensen_bound" = .ok (.str geometryRow074_jensenBoundText) := by rfl

theorem geometryRow074_jensenBound_numerator_no_slash :
    geometryRow074_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow074_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow074_jensenBoundNumeratorChars = some (3535431332395132006584021142566447085839502561840323163116513059790899404233877474579601686282511873927694459990036426381508637921368874958679884726562500000000000000 : Int) := by decide +kernel

theorem geometryRow074_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow074_jensenBoundDenominatorChars = some (91855210519539078772007358433556088501972451628862171539520447209658452581966190868593397271071315503244389713639871666538929088029629750899333374529970577236932512550583653853732339 : Int) := by decide +kernel

theorem geometryRow074_jensenBound_denominator_nonzero : (91855210519539078772007358433556088501972451628862171539520447209658452581966190868593397271071315503244389713639871666538929088029629750899333374529970577236932512550583653853732339 : Int) ≠ 0 := by decide +kernel

theorem geometryRow074_jensenBound_parse :
    parseRational geometryRow074_jensenBoundText = .ok geometryRowsTyped074.jensenBound :=
  original_rational_fraction_of_chars geometryRow074_jensenBoundNumeratorChars geometryRow074_jensenBoundDenominatorChars
    (3535431332395132006584021142566447085839502561840323163116513059790899404233877474579601686282511873927694459990036426381508637921368874958679884726562500000000000000 : Int) (91855210519539078772007358433556088501972451628862171539520447209658452581966190868593397271071315503244389713639871666538929088029629750899333374529970577236932512550583653853732339 : Int)
    geometryRow074_jensenBound_numerator_no_slash geometryRow074_jensenBound_numerator_parse
    geometryRow074_jensenBound_denominator_parse geometryRow074_jensenBound_denominator_nonzero

theorem geometryRow074_jensenBound_read :
    rationalField geometryRowsJson074 "jensen_bound" = .ok geometryRowsTyped074.jensenBound :=
  original_rationalField_of_string geometryRowsJson074 "jensen_bound" geometryRow074_jensenBoundText
    geometryRowsTyped074.jensenBound geometryRow074_jensenBound_field geometryRow074_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_factorMaxima_before"
  err.flush

theorem geometryRow074_factorMaxima_read :
    rationalArrayField geometryRowsJson074 "factor_maxima" = .ok geometryRowsTyped074.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_gapWeightedMeans_before"
  err.flush

theorem geometryRow074_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson074 "gap_weighted_means" = .ok geometryRowsTyped074.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow074_floorChars : List Char := ['3', '0', '4', '9', '4', '2', '6', '6', '6', '3', '7', '3', '2']
noncomputable def geometryRow074_floorText : String := String.ofList geometryRow074_floorChars

theorem geometryRow074_floor_text_read :
    geometryRowsJson074.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow074_floorText := by rfl

theorem geometryRow074_floor_chars_parse :
    SourceJson.intChars geometryRow074_floorChars = some (3049426663732 : Int) := by decide +kernel

theorem geometryRow074_floor_parse :
    parseInteger geometryRow074_floorText = .ok geometryRowsTyped074.jensenFloorQ96 := by
  simp only [geometryRow074_floorText, parseInteger, String.toList_ofList, geometryRow074_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_074 :
    decodeGeometryRow geometryRowsJson074 = .ok geometryRowsTyped074 :=
  original_geometryRow_of_fields geometryRowsJson074 geometryRowsTyped074 geometryRow074_floorText
    geometryRow074_simplexId_read geometryRow074_vertexIds_read
    geometryRow074_physicalVolume_read geometryRow074_meanGap_read
    geometryRow074_factorMaxima_read geometryRow074_gapWeightedMeans_read
    geometryRow074_jensenBound_read geometryRow074_floor_text_read geometryRow074_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_074_original_decoder_complete"
  err.flush

theorem geometryRow074_shape :
    geometryRowsTyped074.simplexId = 74 ∧
    geometryRowsTyped074.vertexIds.size = 9 ∧ geometryRowsTyped074.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped074.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped074.factorMaxima.size = 10 ∧ geometryRowsTyped074.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson075 : SourceJson :=
  (SimplicesBlock009.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped075 : GeometryRow :=
  { simplexId := 75,
    vertexIds := #[32, 30, 28, 26, 23, 22, 13, 8, 0],
    physicalVolume := ((374234946185750005900442616846735343 : ℚ) / (8571411122400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((134535031097 : ℚ) / (1593900000000 : ℚ)), ((68320127833 : ℚ) / (796950000000 : ℚ)), ((999557851 : ℚ) / (8316000000 : ℚ)), ((63918011119 : ℚ) / (683100000000 : ℚ)), ((63546804679 : ℚ) / (683100000000 : ℚ)), ((7774216799 : ℚ) / (108675000000 : ℚ)), ((32067087581 : ℚ) / (869400000000 : ℚ)), ((29350487891 : ℚ) / (869400000000 : ℚ)), ((28877869451 : ℚ) / (869400000000 : ℚ)), ((69980298653 : ℚ) / (2390850000000 : ℚ))],
    jensenBound := ((35795943186365965969333002227041973348851735923184457210762784184500000000000000000000 : ℚ) / (183139598714945760445903344170819794622178183044898968553362844514107039894619370204739384873666244849 : ℚ)),
    jensenFloorQ96 := (15485710485448 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_simplexId_before"
  err.flush

theorem geometryRow075_simplexId_read :
    geometryRowsJson075.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped075.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_vertexIds_before"
  err.flush

theorem geometryRow075_vertexIds_read :
    geometryRowsJson075.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped075.vertexIds := by decide +kernel

noncomputable def geometryRow075_physicalVolumeNumeratorChars : List Char := ['3', '7', '4', '2', '3', '4', '9', '4', '6', '1', '8', '5', '7', '5', '0', '0', '0', '5', '9', '0', '0', '4', '4', '2', '6', '1', '6', '8', '4', '6', '7', '3', '5', '3', '4', '3']
noncomputable def geometryRow075_physicalVolumeDenominatorChars : List Char := ['8', '5', '7', '1', '4', '1', '1', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow075_physicalVolumeText : String := String.ofList (geometryRow075_physicalVolumeNumeratorChars ++ '/' :: geometryRow075_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_physicalVolume_before_field"
  err.flush

theorem geometryRow075_physicalVolume_field :
    geometryRowsJson075.getObjVal? "physical_volume" = .ok (.str geometryRow075_physicalVolumeText) := by rfl

theorem geometryRow075_physicalVolume_numerator_no_slash :
    geometryRow075_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow075_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow075_physicalVolumeNumeratorChars = some (374234946185750005900442616846735343 : Int) := by decide +kernel

theorem geometryRow075_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow075_physicalVolumeDenominatorChars = some (8571411122400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow075_physicalVolume_denominator_nonzero : (8571411122400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow075_physicalVolume_parse :
    parseRational geometryRow075_physicalVolumeText = .ok geometryRowsTyped075.physicalVolume :=
  original_rational_fraction_of_chars geometryRow075_physicalVolumeNumeratorChars geometryRow075_physicalVolumeDenominatorChars
    (374234946185750005900442616846735343 : Int) (8571411122400000000000000000000000000000000000000000000000000 : Int)
    geometryRow075_physicalVolume_numerator_no_slash geometryRow075_physicalVolume_numerator_parse
    geometryRow075_physicalVolume_denominator_parse geometryRow075_physicalVolume_denominator_nonzero

theorem geometryRow075_physicalVolume_read :
    rationalField geometryRowsJson075 "physical_volume" = .ok geometryRowsTyped075.physicalVolume :=
  original_rationalField_of_string geometryRowsJson075 "physical_volume" geometryRow075_physicalVolumeText
    geometryRowsTyped075.physicalVolume geometryRow075_physicalVolume_field geometryRow075_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_physicalVolume_complete"
  err.flush

noncomputable def geometryRow075_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow075_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow075_meanGapText : String := String.ofList (geometryRow075_meanGapNumeratorChars ++ '/' :: geometryRow075_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_meanGap_before_field"
  err.flush

theorem geometryRow075_meanGap_field :
    geometryRowsJson075.getObjVal? "mean_gap" = .ok (.str geometryRow075_meanGapText) := by rfl

theorem geometryRow075_meanGap_numerator_no_slash :
    geometryRow075_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow075_meanGap_numerator_parse :
    SourceJson.intChars geometryRow075_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow075_meanGap_denominator_parse :
    SourceJson.intChars geometryRow075_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow075_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow075_meanGap_parse :
    parseRational geometryRow075_meanGapText = .ok geometryRowsTyped075.meanGap :=
  original_rational_fraction_of_chars geometryRow075_meanGapNumeratorChars geometryRow075_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow075_meanGap_numerator_no_slash geometryRow075_meanGap_numerator_parse
    geometryRow075_meanGap_denominator_parse geometryRow075_meanGap_denominator_nonzero

theorem geometryRow075_meanGap_read :
    rationalField geometryRowsJson075 "mean_gap" = .ok geometryRowsTyped075.meanGap :=
  original_rationalField_of_string geometryRowsJson075 "mean_gap" geometryRow075_meanGapText
    geometryRowsTyped075.meanGap geometryRow075_meanGap_field geometryRow075_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_meanGap_complete"
  err.flush

noncomputable def geometryRow075_jensenBoundNumeratorChars : List Char := ['3', '5', '7', '9', '5', '9', '4', '3', '1', '8', '6', '3', '6', '5', '9', '6', '5', '9', '6', '9', '3', '3', '3', '0', '0', '2', '2', '2', '7', '0', '4', '1', '9', '7', '3', '3', '4', '8', '8', '5', '1', '7', '3', '5', '9', '2', '3', '1', '8', '4', '4', '5', '7', '2', '1', '0', '7', '6', '2', '7', '8', '4', '1', '8', '4', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow075_jensenBoundDenominatorChars : List Char := ['1', '8', '3', '1', '3', '9', '5', '9', '8', '7', '1', '4', '9', '4', '5', '7', '6', '0', '4', '4', '5', '9', '0', '3', '3', '4', '4', '1', '7', '0', '8', '1', '9', '7', '9', '4', '6', '2', '2', '1', '7', '8', '1', '8', '3', '0', '4', '4', '8', '9', '8', '9', '6', '8', '5', '5', '3', '3', '6', '2', '8', '4', '4', '5', '1', '4', '1', '0', '7', '0', '3', '9', '8', '9', '4', '6', '1', '9', '3', '7', '0', '2', '0', '4', '7', '3', '9', '3', '8', '4', '8', '7', '3', '6', '6', '6', '2', '4', '4', '8', '4', '9']
noncomputable def geometryRow075_jensenBoundText : String := String.ofList (geometryRow075_jensenBoundNumeratorChars ++ '/' :: geometryRow075_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_jensenBound_before_field"
  err.flush

theorem geometryRow075_jensenBound_field :
    geometryRowsJson075.getObjVal? "jensen_bound" = .ok (.str geometryRow075_jensenBoundText) := by rfl

theorem geometryRow075_jensenBound_numerator_no_slash :
    geometryRow075_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow075_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow075_jensenBoundNumeratorChars = some (35795943186365965969333002227041973348851735923184457210762784184500000000000000000000 : Int) := by decide +kernel

theorem geometryRow075_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow075_jensenBoundDenominatorChars = some (183139598714945760445903344170819794622178183044898968553362844514107039894619370204739384873666244849 : Int) := by decide +kernel

theorem geometryRow075_jensenBound_denominator_nonzero : (183139598714945760445903344170819794622178183044898968553362844514107039894619370204739384873666244849 : Int) ≠ 0 := by decide +kernel

theorem geometryRow075_jensenBound_parse :
    parseRational geometryRow075_jensenBoundText = .ok geometryRowsTyped075.jensenBound :=
  original_rational_fraction_of_chars geometryRow075_jensenBoundNumeratorChars geometryRow075_jensenBoundDenominatorChars
    (35795943186365965969333002227041973348851735923184457210762784184500000000000000000000 : Int) (183139598714945760445903344170819794622178183044898968553362844514107039894619370204739384873666244849 : Int)
    geometryRow075_jensenBound_numerator_no_slash geometryRow075_jensenBound_numerator_parse
    geometryRow075_jensenBound_denominator_parse geometryRow075_jensenBound_denominator_nonzero

theorem geometryRow075_jensenBound_read :
    rationalField geometryRowsJson075 "jensen_bound" = .ok geometryRowsTyped075.jensenBound :=
  original_rationalField_of_string geometryRowsJson075 "jensen_bound" geometryRow075_jensenBoundText
    geometryRowsTyped075.jensenBound geometryRow075_jensenBound_field geometryRow075_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_factorMaxima_before"
  err.flush

theorem geometryRow075_factorMaxima_read :
    rationalArrayField geometryRowsJson075 "factor_maxima" = .ok geometryRowsTyped075.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_gapWeightedMeans_before"
  err.flush

theorem geometryRow075_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson075 "gap_weighted_means" = .ok geometryRowsTyped075.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow075_floorChars : List Char := ['1', '5', '4', '8', '5', '7', '1', '0', '4', '8', '5', '4', '4', '8']
noncomputable def geometryRow075_floorText : String := String.ofList geometryRow075_floorChars

theorem geometryRow075_floor_text_read :
    geometryRowsJson075.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow075_floorText := by rfl

theorem geometryRow075_floor_chars_parse :
    SourceJson.intChars geometryRow075_floorChars = some (15485710485448 : Int) := by decide +kernel

theorem geometryRow075_floor_parse :
    parseInteger geometryRow075_floorText = .ok geometryRowsTyped075.jensenFloorQ96 := by
  simp only [geometryRow075_floorText, parseInteger, String.toList_ofList, geometryRow075_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_075 :
    decodeGeometryRow geometryRowsJson075 = .ok geometryRowsTyped075 :=
  original_geometryRow_of_fields geometryRowsJson075 geometryRowsTyped075 geometryRow075_floorText
    geometryRow075_simplexId_read geometryRow075_vertexIds_read
    geometryRow075_physicalVolume_read geometryRow075_meanGap_read
    geometryRow075_factorMaxima_read geometryRow075_gapWeightedMeans_read
    geometryRow075_jensenBound_read geometryRow075_floor_text_read geometryRow075_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_075_original_decoder_complete"
  err.flush

theorem geometryRow075_shape :
    geometryRowsTyped075.simplexId = 75 ∧
    geometryRowsTyped075.vertexIds.size = 9 ∧ geometryRowsTyped075.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped075.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped075.factorMaxima.size = 10 ∧ geometryRowsTyped075.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson076 : SourceJson :=
  (SimplicesBlock009.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped076 : GeometryRow :=
  { simplexId := 76,
    vertexIds := #[32, 30, 28, 26, 23, 22, 21, 8, 0],
    physicalVolume := ((15784397483457254566689190950924071 : ℚ) / (399289338000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((496879 : ℚ) / (5600000 : ℚ)), ((10171707 : ℚ) / (110000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((262346643613 : ℚ) / (3187800000000 : ℚ)), ((266557092751 : ℚ) / (3187800000000 : ℚ)), ((578448263147 : ℚ) / (4781700000000 : ℚ)), ((129854367413 : ℚ) / (1366200000000 : ℚ)), ((129111954533 : ℚ) / (1366200000000 : ℚ)), ((30981738629 : ℚ) / (434700000000 : ℚ)), ((15975979507 : ℚ) / (434700000000 : ℚ)), ((7308839831 : ℚ) / (217350000000 : ℚ)), ((7190685221 : ℚ) / (217350000000 : ℚ)), ((273197776031 : ℚ) / (9563400000000 : ℚ))],
    jensenBound := ((3758989823830040726905242617065126026814312059644562328198541659026480000000000000000000000 : ℚ) / (20166222509519900994292174271234769316175439422636871616301968598723546579651312824595963851739769099629653 : ℚ)),
    jensenFloorQ96 := (14768152861116 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_simplexId_before"
  err.flush

theorem geometryRow076_simplexId_read :
    geometryRowsJson076.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped076.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_vertexIds_before"
  err.flush

theorem geometryRow076_vertexIds_read :
    geometryRowsJson076.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped076.vertexIds := by decide +kernel

noncomputable def geometryRow076_physicalVolumeNumeratorChars : List Char := ['1', '5', '7', '8', '4', '3', '9', '7', '4', '8', '3', '4', '5', '7', '2', '5', '4', '5', '6', '6', '6', '8', '9', '1', '9', '0', '9', '5', '0', '9', '2', '4', '0', '7', '1']
noncomputable def geometryRow076_physicalVolumeDenominatorChars : List Char := ['3', '9', '9', '2', '8', '9', '3', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow076_physicalVolumeText : String := String.ofList (geometryRow076_physicalVolumeNumeratorChars ++ '/' :: geometryRow076_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_physicalVolume_before_field"
  err.flush

theorem geometryRow076_physicalVolume_field :
    geometryRowsJson076.getObjVal? "physical_volume" = .ok (.str geometryRow076_physicalVolumeText) := by rfl

theorem geometryRow076_physicalVolume_numerator_no_slash :
    geometryRow076_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow076_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow076_physicalVolumeNumeratorChars = some (15784397483457254566689190950924071 : Int) := by decide +kernel

theorem geometryRow076_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow076_physicalVolumeDenominatorChars = some (399289338000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow076_physicalVolume_denominator_nonzero : (399289338000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow076_physicalVolume_parse :
    parseRational geometryRow076_physicalVolumeText = .ok geometryRowsTyped076.physicalVolume :=
  original_rational_fraction_of_chars geometryRow076_physicalVolumeNumeratorChars geometryRow076_physicalVolumeDenominatorChars
    (15784397483457254566689190950924071 : Int) (399289338000000000000000000000000000000000000000000000000000 : Int)
    geometryRow076_physicalVolume_numerator_no_slash geometryRow076_physicalVolume_numerator_parse
    geometryRow076_physicalVolume_denominator_parse geometryRow076_physicalVolume_denominator_nonzero

theorem geometryRow076_physicalVolume_read :
    rationalField geometryRowsJson076 "physical_volume" = .ok geometryRowsTyped076.physicalVolume :=
  original_rationalField_of_string geometryRowsJson076 "physical_volume" geometryRow076_physicalVolumeText
    geometryRowsTyped076.physicalVolume geometryRow076_physicalVolume_field geometryRow076_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_physicalVolume_complete"
  err.flush

noncomputable def geometryRow076_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow076_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow076_meanGapText : String := String.ofList (geometryRow076_meanGapNumeratorChars ++ '/' :: geometryRow076_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_meanGap_before_field"
  err.flush

theorem geometryRow076_meanGap_field :
    geometryRowsJson076.getObjVal? "mean_gap" = .ok (.str geometryRow076_meanGapText) := by rfl

theorem geometryRow076_meanGap_numerator_no_slash :
    geometryRow076_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow076_meanGap_numerator_parse :
    SourceJson.intChars geometryRow076_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow076_meanGap_denominator_parse :
    SourceJson.intChars geometryRow076_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow076_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow076_meanGap_parse :
    parseRational geometryRow076_meanGapText = .ok geometryRowsTyped076.meanGap :=
  original_rational_fraction_of_chars geometryRow076_meanGapNumeratorChars geometryRow076_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow076_meanGap_numerator_no_slash geometryRow076_meanGap_numerator_parse
    geometryRow076_meanGap_denominator_parse geometryRow076_meanGap_denominator_nonzero

theorem geometryRow076_meanGap_read :
    rationalField geometryRowsJson076 "mean_gap" = .ok geometryRowsTyped076.meanGap :=
  original_rationalField_of_string geometryRowsJson076 "mean_gap" geometryRow076_meanGapText
    geometryRowsTyped076.meanGap geometryRow076_meanGap_field geometryRow076_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_meanGap_complete"
  err.flush

noncomputable def geometryRow076_jensenBoundNumeratorChars : List Char := ['3', '7', '5', '8', '9', '8', '9', '8', '2', '3', '8', '3', '0', '0', '4', '0', '7', '2', '6', '9', '0', '5', '2', '4', '2', '6', '1', '7', '0', '6', '5', '1', '2', '6', '0', '2', '6', '8', '1', '4', '3', '1', '2', '0', '5', '9', '6', '4', '4', '5', '6', '2', '3', '2', '8', '1', '9', '8', '5', '4', '1', '6', '5', '9', '0', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow076_jensenBoundDenominatorChars : List Char := ['2', '0', '1', '6', '6', '2', '2', '2', '5', '0', '9', '5', '1', '9', '9', '0', '0', '9', '9', '4', '2', '9', '2', '1', '7', '4', '2', '7', '1', '2', '3', '4', '7', '6', '9', '3', '1', '6', '1', '7', '5', '4', '3', '9', '4', '2', '2', '6', '3', '6', '8', '7', '1', '6', '1', '6', '3', '0', '1', '9', '6', '8', '5', '9', '8', '7', '2', '3', '5', '4', '6', '5', '7', '9', '6', '5', '1', '3', '1', '2', '8', '2', '4', '5', '9', '5', '9', '6', '3', '8', '5', '1', '7', '3', '9', '7', '6', '9', '0', '9', '9', '6', '2', '9', '6', '5', '3']
noncomputable def geometryRow076_jensenBoundText : String := String.ofList (geometryRow076_jensenBoundNumeratorChars ++ '/' :: geometryRow076_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_jensenBound_before_field"
  err.flush

theorem geometryRow076_jensenBound_field :
    geometryRowsJson076.getObjVal? "jensen_bound" = .ok (.str geometryRow076_jensenBoundText) := by rfl

theorem geometryRow076_jensenBound_numerator_no_slash :
    geometryRow076_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow076_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow076_jensenBoundNumeratorChars = some (3758989823830040726905242617065126026814312059644562328198541659026480000000000000000000000 : Int) := by decide +kernel

theorem geometryRow076_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow076_jensenBoundDenominatorChars = some (20166222509519900994292174271234769316175439422636871616301968598723546579651312824595963851739769099629653 : Int) := by decide +kernel

theorem geometryRow076_jensenBound_denominator_nonzero : (20166222509519900994292174271234769316175439422636871616301968598723546579651312824595963851739769099629653 : Int) ≠ 0 := by decide +kernel

theorem geometryRow076_jensenBound_parse :
    parseRational geometryRow076_jensenBoundText = .ok geometryRowsTyped076.jensenBound :=
  original_rational_fraction_of_chars geometryRow076_jensenBoundNumeratorChars geometryRow076_jensenBoundDenominatorChars
    (3758989823830040726905242617065126026814312059644562328198541659026480000000000000000000000 : Int) (20166222509519900994292174271234769316175439422636871616301968598723546579651312824595963851739769099629653 : Int)
    geometryRow076_jensenBound_numerator_no_slash geometryRow076_jensenBound_numerator_parse
    geometryRow076_jensenBound_denominator_parse geometryRow076_jensenBound_denominator_nonzero

theorem geometryRow076_jensenBound_read :
    rationalField geometryRowsJson076 "jensen_bound" = .ok geometryRowsTyped076.jensenBound :=
  original_rationalField_of_string geometryRowsJson076 "jensen_bound" geometryRow076_jensenBoundText
    geometryRowsTyped076.jensenBound geometryRow076_jensenBound_field geometryRow076_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_factorMaxima_before"
  err.flush

theorem geometryRow076_factorMaxima_read :
    rationalArrayField geometryRowsJson076 "factor_maxima" = .ok geometryRowsTyped076.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_gapWeightedMeans_before"
  err.flush

theorem geometryRow076_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson076 "gap_weighted_means" = .ok geometryRowsTyped076.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow076_floorChars : List Char := ['1', '4', '7', '6', '8', '1', '5', '2', '8', '6', '1', '1', '1', '6']
noncomputable def geometryRow076_floorText : String := String.ofList geometryRow076_floorChars

theorem geometryRow076_floor_text_read :
    geometryRowsJson076.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow076_floorText := by rfl

theorem geometryRow076_floor_chars_parse :
    SourceJson.intChars geometryRow076_floorChars = some (14768152861116 : Int) := by decide +kernel

theorem geometryRow076_floor_parse :
    parseInteger geometryRow076_floorText = .ok geometryRowsTyped076.jensenFloorQ96 := by
  simp only [geometryRow076_floorText, parseInteger, String.toList_ofList, geometryRow076_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_076 :
    decodeGeometryRow geometryRowsJson076 = .ok geometryRowsTyped076 :=
  original_geometryRow_of_fields geometryRowsJson076 geometryRowsTyped076 geometryRow076_floorText
    geometryRow076_simplexId_read geometryRow076_vertexIds_read
    geometryRow076_physicalVolume_read geometryRow076_meanGap_read
    geometryRow076_factorMaxima_read geometryRow076_gapWeightedMeans_read
    geometryRow076_jensenBound_read geometryRow076_floor_text_read geometryRow076_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_076_original_decoder_complete"
  err.flush

theorem geometryRow076_shape :
    geometryRowsTyped076.simplexId = 76 ∧
    geometryRowsTyped076.vertexIds.size = 9 ∧ geometryRowsTyped076.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped076.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped076.factorMaxima.size = 10 ∧ geometryRowsTyped076.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson077 : SourceJson :=
  (SimplicesBlock009.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped077 : GeometryRow :=
  { simplexId := 77,
    vertexIds := #[32, 30, 28, 26, 25, 14, 4, 3, 0],
    physicalVolume := ((1364910643953636985829949354327061640041 : ℚ) / (82075526498649600000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((330368039 : ℚ) / (148995000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((32031 : ℚ) / (418750 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((522463505581951422677927 : ℚ) / (6068234366480840400000000 : ℚ)), ((67326365714400613937467 : ℚ) / (758529295810105050000000 : ℚ)), ((143956236384174767801813 : ℚ) / (1213646873296168080000000 : ℚ)), ((9021230021799940284157 : ℚ) / (96321180420330800000000 : ℚ)), ((26906663089201188002711 : ℚ) / (288963541260992400000000 : ℚ)), ((39108932669780263050487 : ℚ) / (551657669680076400000000 : ℚ)), ((39478302943338410776627 : ℚ) / (1103315339360152800000000 : ℚ)), ((37754575000067054721307 : ℚ) / (1103315339360152800000000 : ℚ)), ((17705004072379238582801 : ℚ) / (551657669680076400000000 : ℚ)), ((22968833410339692553949 : ℚ) / (758529295810105050000000 : ℚ))],
    jensenBound := ((6444359366398911540307062866044381149636965967050807770225315812582536546740848307475604310600700462975474234162400362604169202826264926864800196028290501916403240335439896814922421846097920000000000000000000000000 : ℚ) / (29136421206371031546146368310890886859526932129338216848929528811183420054315863304511315869858906889192678881059744969228887353943424297991846109313100888359556870736907032470221654899375963755121860625973363954156337436146313 : ℚ)),
    jensenFloorQ96 := (17523591781056870 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_simplexId_before"
  err.flush

theorem geometryRow077_simplexId_read :
    geometryRowsJson077.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped077.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_vertexIds_before"
  err.flush

theorem geometryRow077_vertexIds_read :
    geometryRowsJson077.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped077.vertexIds := by decide +kernel

noncomputable def geometryRow077_physicalVolumeNumeratorChars : List Char := ['1', '3', '6', '4', '9', '1', '0', '6', '4', '3', '9', '5', '3', '6', '3', '6', '9', '8', '5', '8', '2', '9', '9', '4', '9', '3', '5', '4', '3', '2', '7', '0', '6', '1', '6', '4', '0', '0', '4', '1']
noncomputable def geometryRow077_physicalVolumeDenominatorChars : List Char := ['8', '2', '0', '7', '5', '5', '2', '6', '4', '9', '8', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow077_physicalVolumeText : String := String.ofList (geometryRow077_physicalVolumeNumeratorChars ++ '/' :: geometryRow077_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_physicalVolume_before_field"
  err.flush

theorem geometryRow077_physicalVolume_field :
    geometryRowsJson077.getObjVal? "physical_volume" = .ok (.str geometryRow077_physicalVolumeText) := by rfl

theorem geometryRow077_physicalVolume_numerator_no_slash :
    geometryRow077_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow077_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow077_physicalVolumeNumeratorChars = some (1364910643953636985829949354327061640041 : Int) := by decide +kernel

theorem geometryRow077_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow077_physicalVolumeDenominatorChars = some (82075526498649600000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow077_physicalVolume_denominator_nonzero : (82075526498649600000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow077_physicalVolume_parse :
    parseRational geometryRow077_physicalVolumeText = .ok geometryRowsTyped077.physicalVolume :=
  original_rational_fraction_of_chars geometryRow077_physicalVolumeNumeratorChars geometryRow077_physicalVolumeDenominatorChars
    (1364910643953636985829949354327061640041 : Int) (82075526498649600000000000000000000000000000000000000000000000 : Int)
    geometryRow077_physicalVolume_numerator_no_slash geometryRow077_physicalVolume_numerator_parse
    geometryRow077_physicalVolume_denominator_parse geometryRow077_physicalVolume_denominator_nonzero

theorem geometryRow077_physicalVolume_read :
    rationalField geometryRowsJson077 "physical_volume" = .ok geometryRowsTyped077.physicalVolume :=
  original_rationalField_of_string geometryRowsJson077 "physical_volume" geometryRow077_physicalVolumeText
    geometryRowsTyped077.physicalVolume geometryRow077_physicalVolume_field geometryRow077_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_physicalVolume_complete"
  err.flush

noncomputable def geometryRow077_meanGapNumeratorChars : List Char := ['3', '3', '0', '3', '6', '8', '0', '3', '9']
noncomputable def geometryRow077_meanGapDenominatorChars : List Char := ['1', '4', '8', '9', '9', '5', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow077_meanGapText : String := String.ofList (geometryRow077_meanGapNumeratorChars ++ '/' :: geometryRow077_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_meanGap_before_field"
  err.flush

theorem geometryRow077_meanGap_field :
    geometryRowsJson077.getObjVal? "mean_gap" = .ok (.str geometryRow077_meanGapText) := by rfl

theorem geometryRow077_meanGap_numerator_no_slash :
    geometryRow077_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow077_meanGap_numerator_parse :
    SourceJson.intChars geometryRow077_meanGapNumeratorChars = some (330368039 : Int) := by decide +kernel

theorem geometryRow077_meanGap_denominator_parse :
    SourceJson.intChars geometryRow077_meanGapDenominatorChars = some (148995000000 : Int) := by decide +kernel

theorem geometryRow077_meanGap_denominator_nonzero : (148995000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow077_meanGap_parse :
    parseRational geometryRow077_meanGapText = .ok geometryRowsTyped077.meanGap :=
  original_rational_fraction_of_chars geometryRow077_meanGapNumeratorChars geometryRow077_meanGapDenominatorChars
    (330368039 : Int) (148995000000 : Int)
    geometryRow077_meanGap_numerator_no_slash geometryRow077_meanGap_numerator_parse
    geometryRow077_meanGap_denominator_parse geometryRow077_meanGap_denominator_nonzero

theorem geometryRow077_meanGap_read :
    rationalField geometryRowsJson077 "mean_gap" = .ok geometryRowsTyped077.meanGap :=
  original_rationalField_of_string geometryRowsJson077 "mean_gap" geometryRow077_meanGapText
    geometryRowsTyped077.meanGap geometryRow077_meanGap_field geometryRow077_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_meanGap_complete"
  err.flush

noncomputable def geometryRow077_jensenBoundNumeratorChars : List Char := ['6', '4', '4', '4', '3', '5', '9', '3', '6', '6', '3', '9', '8', '9', '1', '1', '5', '4', '0', '3', '0', '7', '0', '6', '2', '8', '6', '6', '0', '4', '4', '3', '8', '1', '1', '4', '9', '6', '3', '6', '9', '6', '5', '9', '6', '7', '0', '5', '0', '8', '0', '7', '7', '7', '0', '2', '2', '5', '3', '1', '5', '8', '1', '2', '5', '8', '2', '5', '3', '6', '5', '4', '6', '7', '4', '0', '8', '4', '8', '3', '0', '7', '4', '7', '5', '6', '0', '4', '3', '1', '0', '6', '0', '0', '7', '0', '0', '4', '6', '2', '9', '7', '5', '4', '7', '4', '2', '3', '4', '1', '6', '2', '4', '0', '0', '3', '6', '2', '6', '0', '4', '1', '6', '9', '2', '0', '2', '8', '2', '6', '2', '6', '4', '9', '2', '6', '8', '6', '4', '8', '0', '0', '1', '9', '6', '0', '2', '8', '2', '9', '0', '5', '0', '1', '9', '1', '6', '4', '0', '3', '2', '4', '0', '3', '3', '5', '4', '3', '9', '8', '9', '6', '8', '1', '4', '9', '2', '2', '4', '2', '1', '8', '4', '6', '0', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow077_jensenBoundDenominatorChars : List Char := ['2', '9', '1', '3', '6', '4', '2', '1', '2', '0', '6', '3', '7', '1', '0', '3', '1', '5', '4', '6', '1', '4', '6', '3', '6', '8', '3', '1', '0', '8', '9', '0', '8', '8', '6', '8', '5', '9', '5', '2', '6', '9', '3', '2', '1', '2', '9', '3', '3', '8', '2', '1', '6', '8', '4', '8', '9', '2', '9', '5', '2', '8', '8', '1', '1', '1', '8', '3', '4', '2', '0', '0', '5', '4', '3', '1', '5', '8', '6', '3', '3', '0', '4', '5', '1', '1', '3', '1', '5', '8', '6', '9', '8', '5', '8', '9', '0', '6', '8', '8', '9', '1', '9', '2', '6', '7', '8', '8', '8', '1', '0', '5', '9', '7', '4', '4', '9', '6', '9', '2', '2', '8', '8', '8', '7', '3', '5', '3', '9', '4', '3', '4', '2', '4', '2', '9', '7', '9', '9', '1', '8', '4', '6', '1', '0', '9', '3', '1', '3', '1', '0', '0', '8', '8', '8', '3', '5', '9', '5', '5', '6', '8', '7', '0', '7', '3', '6', '9', '0', '7', '0', '3', '2', '4', '7', '0', '2', '2', '1', '6', '5', '4', '8', '9', '9', '3', '7', '5', '9', '6', '3', '7', '5', '5', '1', '2', '1', '8', '6', '0', '6', '2', '5', '9', '7', '3', '3', '6', '3', '9', '5', '4', '1', '5', '6', '3', '3', '7', '4', '3', '6', '1', '4', '6', '3', '1', '3']
noncomputable def geometryRow077_jensenBoundText : String := String.ofList (geometryRow077_jensenBoundNumeratorChars ++ '/' :: geometryRow077_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_jensenBound_before_field"
  err.flush

theorem geometryRow077_jensenBound_field :
    geometryRowsJson077.getObjVal? "jensen_bound" = .ok (.str geometryRow077_jensenBoundText) := by rfl

theorem geometryRow077_jensenBound_numerator_no_slash :
    geometryRow077_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow077_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow077_jensenBoundNumeratorChars = some (6444359366398911540307062866044381149636965967050807770225315812582536546740848307475604310600700462975474234162400362604169202826264926864800196028290501916403240335439896814922421846097920000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow077_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow077_jensenBoundDenominatorChars = some (29136421206371031546146368310890886859526932129338216848929528811183420054315863304511315869858906889192678881059744969228887353943424297991846109313100888359556870736907032470221654899375963755121860625973363954156337436146313 : Int) := by decide +kernel

theorem geometryRow077_jensenBound_denominator_nonzero : (29136421206371031546146368310890886859526932129338216848929528811183420054315863304511315869858906889192678881059744969228887353943424297991846109313100888359556870736907032470221654899375963755121860625973363954156337436146313 : Int) ≠ 0 := by decide +kernel

theorem geometryRow077_jensenBound_parse :
    parseRational geometryRow077_jensenBoundText = .ok geometryRowsTyped077.jensenBound :=
  original_rational_fraction_of_chars geometryRow077_jensenBoundNumeratorChars geometryRow077_jensenBoundDenominatorChars
    (6444359366398911540307062866044381149636965967050807770225315812582536546740848307475604310600700462975474234162400362604169202826264926864800196028290501916403240335439896814922421846097920000000000000000000000000 : Int) (29136421206371031546146368310890886859526932129338216848929528811183420054315863304511315869858906889192678881059744969228887353943424297991846109313100888359556870736907032470221654899375963755121860625973363954156337436146313 : Int)
    geometryRow077_jensenBound_numerator_no_slash geometryRow077_jensenBound_numerator_parse
    geometryRow077_jensenBound_denominator_parse geometryRow077_jensenBound_denominator_nonzero

theorem geometryRow077_jensenBound_read :
    rationalField geometryRowsJson077 "jensen_bound" = .ok geometryRowsTyped077.jensenBound :=
  original_rationalField_of_string geometryRowsJson077 "jensen_bound" geometryRow077_jensenBoundText
    geometryRowsTyped077.jensenBound geometryRow077_jensenBound_field geometryRow077_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_factorMaxima_before"
  err.flush

theorem geometryRow077_factorMaxima_read :
    rationalArrayField geometryRowsJson077 "factor_maxima" = .ok geometryRowsTyped077.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_gapWeightedMeans_before"
  err.flush

theorem geometryRow077_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson077 "gap_weighted_means" = .ok geometryRowsTyped077.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow077_floorChars : List Char := ['1', '7', '5', '2', '3', '5', '9', '1', '7', '8', '1', '0', '5', '6', '8', '7', '0']
noncomputable def geometryRow077_floorText : String := String.ofList geometryRow077_floorChars

theorem geometryRow077_floor_text_read :
    geometryRowsJson077.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow077_floorText := by rfl

theorem geometryRow077_floor_chars_parse :
    SourceJson.intChars geometryRow077_floorChars = some (17523591781056870 : Int) := by decide +kernel

theorem geometryRow077_floor_parse :
    parseInteger geometryRow077_floorText = .ok geometryRowsTyped077.jensenFloorQ96 := by
  simp only [geometryRow077_floorText, parseInteger, String.toList_ofList, geometryRow077_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_077 :
    decodeGeometryRow geometryRowsJson077 = .ok geometryRowsTyped077 :=
  original_geometryRow_of_fields geometryRowsJson077 geometryRowsTyped077 geometryRow077_floorText
    geometryRow077_simplexId_read geometryRow077_vertexIds_read
    geometryRow077_physicalVolume_read geometryRow077_meanGap_read
    geometryRow077_factorMaxima_read geometryRow077_gapWeightedMeans_read
    geometryRow077_jensenBound_read geometryRow077_floor_text_read geometryRow077_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_077_original_decoder_complete"
  err.flush

theorem geometryRow077_shape :
    geometryRowsTyped077.simplexId = 77 ∧
    geometryRowsTyped077.vertexIds.size = 9 ∧ geometryRowsTyped077.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped077.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped077.factorMaxima.size = 10 ∧ geometryRowsTyped077.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson078 : SourceJson :=
  (SimplicesBlock009.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped078 : GeometryRow :=
  { simplexId := 78,
    vertexIds := #[32, 30, 28, 26, 25, 14, 11, 3, 0],
    physicalVolume := ((36167497943257494121629841289790160723 : ℚ) / (254497756584960000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((31729387 : ℚ) / (21285000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((50560479126705161234461 : ℚ) / (582808667580493200000000 : ℚ)), ((12933359420123357597377 : ℚ) / (145702166895123300000000 : ℚ)), ((1982147117044954269787 : ℚ) / (16651676216585520000000 : ℚ)), ((18024352963362847823921 : ℚ) / (194269555860164400000000 : ℚ)), ((5972928023735874973787 : ℚ) / (64756518620054800000000 : ℚ)), ((543763146621908176313 : ℚ) / (7568943734811600000000 : ℚ)), ((3841817287191232462811 : ℚ) / (105965212287362400000000 : ℚ)), ((3676266069947814729251 : ℚ) / (105965212287362400000000 : ℚ)), ((1672123315539867381523 : ℚ) / (52982606143681200000000 : ℚ)), ((4412293232849138816819 : ℚ) / (145702166895123300000000 : ℚ))],
    jensenBound := ((1412810536957565366860126163376407264325394988030953008716283440989649183232816679618157856596485480115933652394246741564299311745013026507018595936942882398275546429685827894476800000000000000000000000000 : ℚ) / (1129518685213386472019035371050918700121186732329335462404946243247871488003905477288025054208224412714089995625561696243378836574870317551526956695630618704269229945724977380078252182231573194023686575689855235760739 : ℚ)),
    jensenFloorQ96 := (99099186484721698 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_simplexId_before"
  err.flush

theorem geometryRow078_simplexId_read :
    geometryRowsJson078.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped078.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_vertexIds_before"
  err.flush

theorem geometryRow078_vertexIds_read :
    geometryRowsJson078.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped078.vertexIds := by decide +kernel

noncomputable def geometryRow078_physicalVolumeNumeratorChars : List Char := ['3', '6', '1', '6', '7', '4', '9', '7', '9', '4', '3', '2', '5', '7', '4', '9', '4', '1', '2', '1', '6', '2', '9', '8', '4', '1', '2', '8', '9', '7', '9', '0', '1', '6', '0', '7', '2', '3']
noncomputable def geometryRow078_physicalVolumeDenominatorChars : List Char := ['2', '5', '4', '4', '9', '7', '7', '5', '6', '5', '8', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow078_physicalVolumeText : String := String.ofList (geometryRow078_physicalVolumeNumeratorChars ++ '/' :: geometryRow078_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_physicalVolume_before_field"
  err.flush

theorem geometryRow078_physicalVolume_field :
    geometryRowsJson078.getObjVal? "physical_volume" = .ok (.str geometryRow078_physicalVolumeText) := by rfl

theorem geometryRow078_physicalVolume_numerator_no_slash :
    geometryRow078_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow078_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow078_physicalVolumeNumeratorChars = some (36167497943257494121629841289790160723 : Int) := by decide +kernel

theorem geometryRow078_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow078_physicalVolumeDenominatorChars = some (254497756584960000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow078_physicalVolume_denominator_nonzero : (254497756584960000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow078_physicalVolume_parse :
    parseRational geometryRow078_physicalVolumeText = .ok geometryRowsTyped078.physicalVolume :=
  original_rational_fraction_of_chars geometryRow078_physicalVolumeNumeratorChars geometryRow078_physicalVolumeDenominatorChars
    (36167497943257494121629841289790160723 : Int) (254497756584960000000000000000000000000000000000000000000000 : Int)
    geometryRow078_physicalVolume_numerator_no_slash geometryRow078_physicalVolume_numerator_parse
    geometryRow078_physicalVolume_denominator_parse geometryRow078_physicalVolume_denominator_nonzero

theorem geometryRow078_physicalVolume_read :
    rationalField geometryRowsJson078 "physical_volume" = .ok geometryRowsTyped078.physicalVolume :=
  original_rationalField_of_string geometryRowsJson078 "physical_volume" geometryRow078_physicalVolumeText
    geometryRowsTyped078.physicalVolume geometryRow078_physicalVolume_field geometryRow078_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_physicalVolume_complete"
  err.flush

noncomputable def geometryRow078_meanGapNumeratorChars : List Char := ['3', '1', '7', '2', '9', '3', '8', '7']
noncomputable def geometryRow078_meanGapDenominatorChars : List Char := ['2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow078_meanGapText : String := String.ofList (geometryRow078_meanGapNumeratorChars ++ '/' :: geometryRow078_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_meanGap_before_field"
  err.flush

theorem geometryRow078_meanGap_field :
    geometryRowsJson078.getObjVal? "mean_gap" = .ok (.str geometryRow078_meanGapText) := by rfl

theorem geometryRow078_meanGap_numerator_no_slash :
    geometryRow078_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow078_meanGap_numerator_parse :
    SourceJson.intChars geometryRow078_meanGapNumeratorChars = some (31729387 : Int) := by decide +kernel

theorem geometryRow078_meanGap_denominator_parse :
    SourceJson.intChars geometryRow078_meanGapDenominatorChars = some (21285000000 : Int) := by decide +kernel

theorem geometryRow078_meanGap_denominator_nonzero : (21285000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow078_meanGap_parse :
    parseRational geometryRow078_meanGapText = .ok geometryRowsTyped078.meanGap :=
  original_rational_fraction_of_chars geometryRow078_meanGapNumeratorChars geometryRow078_meanGapDenominatorChars
    (31729387 : Int) (21285000000 : Int)
    geometryRow078_meanGap_numerator_no_slash geometryRow078_meanGap_numerator_parse
    geometryRow078_meanGap_denominator_parse geometryRow078_meanGap_denominator_nonzero

theorem geometryRow078_meanGap_read :
    rationalField geometryRowsJson078 "mean_gap" = .ok geometryRowsTyped078.meanGap :=
  original_rationalField_of_string geometryRowsJson078 "mean_gap" geometryRow078_meanGapText
    geometryRowsTyped078.meanGap geometryRow078_meanGap_field geometryRow078_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_meanGap_complete"
  err.flush

noncomputable def geometryRow078_jensenBoundNumeratorChars : List Char := ['1', '4', '1', '2', '8', '1', '0', '5', '3', '6', '9', '5', '7', '5', '6', '5', '3', '6', '6', '8', '6', '0', '1', '2', '6', '1', '6', '3', '3', '7', '6', '4', '0', '7', '2', '6', '4', '3', '2', '5', '3', '9', '4', '9', '8', '8', '0', '3', '0', '9', '5', '3', '0', '0', '8', '7', '1', '6', '2', '8', '3', '4', '4', '0', '9', '8', '9', '6', '4', '9', '1', '8', '3', '2', '3', '2', '8', '1', '6', '6', '7', '9', '6', '1', '8', '1', '5', '7', '8', '5', '6', '5', '9', '6', '4', '8', '5', '4', '8', '0', '1', '1', '5', '9', '3', '3', '6', '5', '2', '3', '9', '4', '2', '4', '6', '7', '4', '1', '5', '6', '4', '2', '9', '9', '3', '1', '1', '7', '4', '5', '0', '1', '3', '0', '2', '6', '5', '0', '7', '0', '1', '8', '5', '9', '5', '9', '3', '6', '9', '4', '2', '8', '8', '2', '3', '9', '8', '2', '7', '5', '5', '4', '6', '4', '2', '9', '6', '8', '5', '8', '2', '7', '8', '9', '4', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow078_jensenBoundDenominatorChars : List Char := ['1', '1', '2', '9', '5', '1', '8', '6', '8', '5', '2', '1', '3', '3', '8', '6', '4', '7', '2', '0', '1', '9', '0', '3', '5', '3', '7', '1', '0', '5', '0', '9', '1', '8', '7', '0', '0', '1', '2', '1', '1', '8', '6', '7', '3', '2', '3', '2', '9', '3', '3', '5', '4', '6', '2', '4', '0', '4', '9', '4', '6', '2', '4', '3', '2', '4', '7', '8', '7', '1', '4', '8', '8', '0', '0', '3', '9', '0', '5', '4', '7', '7', '2', '8', '8', '0', '2', '5', '0', '5', '4', '2', '0', '8', '2', '2', '4', '4', '1', '2', '7', '1', '4', '0', '8', '9', '9', '9', '5', '6', '2', '5', '5', '6', '1', '6', '9', '6', '2', '4', '3', '3', '7', '8', '8', '3', '6', '5', '7', '4', '8', '7', '0', '3', '1', '7', '5', '5', '1', '5', '2', '6', '9', '5', '6', '6', '9', '5', '6', '3', '0', '6', '1', '8', '7', '0', '4', '2', '6', '9', '2', '2', '9', '9', '4', '5', '7', '2', '4', '9', '7', '7', '3', '8', '0', '0', '7', '8', '2', '5', '2', '1', '8', '2', '2', '3', '1', '5', '7', '3', '1', '9', '4', '0', '2', '3', '6', '8', '6', '5', '7', '5', '6', '8', '9', '8', '5', '5', '2', '3', '5', '7', '6', '0', '7', '3', '9']
noncomputable def geometryRow078_jensenBoundText : String := String.ofList (geometryRow078_jensenBoundNumeratorChars ++ '/' :: geometryRow078_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_jensenBound_before_field"
  err.flush

theorem geometryRow078_jensenBound_field :
    geometryRowsJson078.getObjVal? "jensen_bound" = .ok (.str geometryRow078_jensenBoundText) := by rfl

theorem geometryRow078_jensenBound_numerator_no_slash :
    geometryRow078_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow078_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow078_jensenBoundNumeratorChars = some (1412810536957565366860126163376407264325394988030953008716283440989649183232816679618157856596485480115933652394246741564299311745013026507018595936942882398275546429685827894476800000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow078_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow078_jensenBoundDenominatorChars = some (1129518685213386472019035371050918700121186732329335462404946243247871488003905477288025054208224412714089995625561696243378836574870317551526956695630618704269229945724977380078252182231573194023686575689855235760739 : Int) := by decide +kernel

theorem geometryRow078_jensenBound_denominator_nonzero : (1129518685213386472019035371050918700121186732329335462404946243247871488003905477288025054208224412714089995625561696243378836574870317551526956695630618704269229945724977380078252182231573194023686575689855235760739 : Int) ≠ 0 := by decide +kernel

theorem geometryRow078_jensenBound_parse :
    parseRational geometryRow078_jensenBoundText = .ok geometryRowsTyped078.jensenBound :=
  original_rational_fraction_of_chars geometryRow078_jensenBoundNumeratorChars geometryRow078_jensenBoundDenominatorChars
    (1412810536957565366860126163376407264325394988030953008716283440989649183232816679618157856596485480115933652394246741564299311745013026507018595936942882398275546429685827894476800000000000000000000000000 : Int) (1129518685213386472019035371050918700121186732329335462404946243247871488003905477288025054208224412714089995625561696243378836574870317551526956695630618704269229945724977380078252182231573194023686575689855235760739 : Int)
    geometryRow078_jensenBound_numerator_no_slash geometryRow078_jensenBound_numerator_parse
    geometryRow078_jensenBound_denominator_parse geometryRow078_jensenBound_denominator_nonzero

theorem geometryRow078_jensenBound_read :
    rationalField geometryRowsJson078 "jensen_bound" = .ok geometryRowsTyped078.jensenBound :=
  original_rationalField_of_string geometryRowsJson078 "jensen_bound" geometryRow078_jensenBoundText
    geometryRowsTyped078.jensenBound geometryRow078_jensenBound_field geometryRow078_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_factorMaxima_before"
  err.flush

theorem geometryRow078_factorMaxima_read :
    rationalArrayField geometryRowsJson078 "factor_maxima" = .ok geometryRowsTyped078.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_gapWeightedMeans_before"
  err.flush

theorem geometryRow078_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson078 "gap_weighted_means" = .ok geometryRowsTyped078.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow078_floorChars : List Char := ['9', '9', '0', '9', '9', '1', '8', '6', '4', '8', '4', '7', '2', '1', '6', '9', '8']
noncomputable def geometryRow078_floorText : String := String.ofList geometryRow078_floorChars

theorem geometryRow078_floor_text_read :
    geometryRowsJson078.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow078_floorText := by rfl

theorem geometryRow078_floor_chars_parse :
    SourceJson.intChars geometryRow078_floorChars = some (99099186484721698 : Int) := by decide +kernel

theorem geometryRow078_floor_parse :
    parseInteger geometryRow078_floorText = .ok geometryRowsTyped078.jensenFloorQ96 := by
  simp only [geometryRow078_floorText, parseInteger, String.toList_ofList, geometryRow078_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_078 :
    decodeGeometryRow geometryRowsJson078 = .ok geometryRowsTyped078 :=
  original_geometryRow_of_fields geometryRowsJson078 geometryRowsTyped078 geometryRow078_floorText
    geometryRow078_simplexId_read geometryRow078_vertexIds_read
    geometryRow078_physicalVolume_read geometryRow078_meanGap_read
    geometryRow078_factorMaxima_read geometryRow078_gapWeightedMeans_read
    geometryRow078_jensenBound_read geometryRow078_floor_text_read geometryRow078_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_078_original_decoder_complete"
  err.flush

theorem geometryRow078_shape :
    geometryRowsTyped078.simplexId = 78 ∧
    geometryRowsTyped078.vertexIds.size = 9 ∧ geometryRowsTyped078.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped078.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped078.factorMaxima.size = 10 ∧ geometryRowsTyped078.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson079 : SourceJson :=
  (SimplicesBlock009.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped079 : GeometryRow :=
  { simplexId := 79,
    vertexIds := #[32, 30, 28, 26, 25, 14, 11, 8, 0],
    physicalVolume := ((20009371043470243065124318486771893930509 : ℚ) / (31960183385088000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((18332084289793 : ℚ) / (213582600000000 : ℚ)), ((18614184382039 : ℚ) / (213582600000000 : ℚ)), ((2182719445529 : ℚ) / (18307080000000 : ℚ)), ((7378744060099 : ℚ) / (80093475000000 : ℚ)), ((7335220105009 : ℚ) / (80093475000000 : ℚ)), ((607734095347 : ℚ) / (8321400000000 : ℚ)), ((4293140653159 : ℚ) / (116499600000000 : ℚ)), ((4111131386419 : ℚ) / (116499600000000 : ℚ)), ((944907930121 : ℚ) / (29124900000000 : ℚ)), ((19059110161799 : ℚ) / (640747800000000 : ℚ))],
    jensenBound := ((72295130845170338754093143846342471581117473855358610617629751676393326159523119675333242375000000000000000000000 : ℚ) / (27133740312078666841442775879896045024462676063740773841260944145524795760549187848876984780674103116812782182831713215847987 : ℚ)),
    jensenFloorQ96 := (211095496223991202 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_simplexId_before"
  err.flush

theorem geometryRow079_simplexId_read :
    geometryRowsJson079.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped079.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_vertexIds_before"
  err.flush

theorem geometryRow079_vertexIds_read :
    geometryRowsJson079.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped079.vertexIds := by decide +kernel

noncomputable def geometryRow079_physicalVolumeNumeratorChars : List Char := ['2', '0', '0', '0', '9', '3', '7', '1', '0', '4', '3', '4', '7', '0', '2', '4', '3', '0', '6', '5', '1', '2', '4', '3', '1', '8', '4', '8', '6', '7', '7', '1', '8', '9', '3', '9', '3', '0', '5', '0', '9']
noncomputable def geometryRow079_physicalVolumeDenominatorChars : List Char := ['3', '1', '9', '6', '0', '1', '8', '3', '3', '8', '5', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow079_physicalVolumeText : String := String.ofList (geometryRow079_physicalVolumeNumeratorChars ++ '/' :: geometryRow079_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_physicalVolume_before_field"
  err.flush

theorem geometryRow079_physicalVolume_field :
    geometryRowsJson079.getObjVal? "physical_volume" = .ok (.str geometryRow079_physicalVolumeText) := by rfl

theorem geometryRow079_physicalVolume_numerator_no_slash :
    geometryRow079_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow079_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow079_physicalVolumeNumeratorChars = some (20009371043470243065124318486771893930509 : Int) := by decide +kernel

theorem geometryRow079_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow079_physicalVolumeDenominatorChars = some (31960183385088000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow079_physicalVolume_denominator_nonzero : (31960183385088000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow079_physicalVolume_parse :
    parseRational geometryRow079_physicalVolumeText = .ok geometryRowsTyped079.physicalVolume :=
  original_rational_fraction_of_chars geometryRow079_physicalVolumeNumeratorChars geometryRow079_physicalVolumeDenominatorChars
    (20009371043470243065124318486771893930509 : Int) (31960183385088000000000000000000000000000000000000000000000000 : Int)
    geometryRow079_physicalVolume_numerator_no_slash geometryRow079_physicalVolume_numerator_parse
    geometryRow079_physicalVolume_denominator_parse geometryRow079_physicalVolume_denominator_nonzero

theorem geometryRow079_physicalVolume_read :
    rationalField geometryRowsJson079 "physical_volume" = .ok geometryRowsTyped079.physicalVolume :=
  original_rationalField_of_string geometryRowsJson079 "physical_volume" geometryRow079_physicalVolumeText
    geometryRowsTyped079.physicalVolume geometryRow079_physicalVolume_field geometryRow079_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_physicalVolume_complete"
  err.flush

noncomputable def geometryRow079_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow079_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow079_meanGapText : String := String.ofList (geometryRow079_meanGapNumeratorChars ++ '/' :: geometryRow079_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_meanGap_before_field"
  err.flush

theorem geometryRow079_meanGap_field :
    geometryRowsJson079.getObjVal? "mean_gap" = .ok (.str geometryRow079_meanGapText) := by rfl

theorem geometryRow079_meanGap_numerator_no_slash :
    geometryRow079_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow079_meanGap_numerator_parse :
    SourceJson.intChars geometryRow079_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow079_meanGap_denominator_parse :
    SourceJson.intChars geometryRow079_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow079_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow079_meanGap_parse :
    parseRational geometryRow079_meanGapText = .ok geometryRowsTyped079.meanGap :=
  original_rational_fraction_of_chars geometryRow079_meanGapNumeratorChars geometryRow079_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow079_meanGap_numerator_no_slash geometryRow079_meanGap_numerator_parse
    geometryRow079_meanGap_denominator_parse geometryRow079_meanGap_denominator_nonzero

theorem geometryRow079_meanGap_read :
    rationalField geometryRowsJson079 "mean_gap" = .ok geometryRowsTyped079.meanGap :=
  original_rationalField_of_string geometryRowsJson079 "mean_gap" geometryRow079_meanGapText
    geometryRowsTyped079.meanGap geometryRow079_meanGap_field geometryRow079_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_meanGap_complete"
  err.flush

noncomputable def geometryRow079_jensenBoundNumeratorChars : List Char := ['7', '2', '2', '9', '5', '1', '3', '0', '8', '4', '5', '1', '7', '0', '3', '3', '8', '7', '5', '4', '0', '9', '3', '1', '4', '3', '8', '4', '6', '3', '4', '2', '4', '7', '1', '5', '8', '1', '1', '1', '7', '4', '7', '3', '8', '5', '5', '3', '5', '8', '6', '1', '0', '6', '1', '7', '6', '2', '9', '7', '5', '1', '6', '7', '6', '3', '9', '3', '3', '2', '6', '1', '5', '9', '5', '2', '3', '1', '1', '9', '6', '7', '5', '3', '3', '3', '2', '4', '2', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow079_jensenBoundDenominatorChars : List Char := ['2', '7', '1', '3', '3', '7', '4', '0', '3', '1', '2', '0', '7', '8', '6', '6', '6', '8', '4', '1', '4', '4', '2', '7', '7', '5', '8', '7', '9', '8', '9', '6', '0', '4', '5', '0', '2', '4', '4', '6', '2', '6', '7', '6', '0', '6', '3', '7', '4', '0', '7', '7', '3', '8', '4', '1', '2', '6', '0', '9', '4', '4', '1', '4', '5', '5', '2', '4', '7', '9', '5', '7', '6', '0', '5', '4', '9', '1', '8', '7', '8', '4', '8', '8', '7', '6', '9', '8', '4', '7', '8', '0', '6', '7', '4', '1', '0', '3', '1', '1', '6', '8', '1', '2', '7', '8', '2', '1', '8', '2', '8', '3', '1', '7', '1', '3', '2', '1', '5', '8', '4', '7', '9', '8', '7']
noncomputable def geometryRow079_jensenBoundText : String := String.ofList (geometryRow079_jensenBoundNumeratorChars ++ '/' :: geometryRow079_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_jensenBound_before_field"
  err.flush

theorem geometryRow079_jensenBound_field :
    geometryRowsJson079.getObjVal? "jensen_bound" = .ok (.str geometryRow079_jensenBoundText) := by rfl

theorem geometryRow079_jensenBound_numerator_no_slash :
    geometryRow079_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow079_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow079_jensenBoundNumeratorChars = some (72295130845170338754093143846342471581117473855358610617629751676393326159523119675333242375000000000000000000000 : Int) := by decide +kernel

theorem geometryRow079_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow079_jensenBoundDenominatorChars = some (27133740312078666841442775879896045024462676063740773841260944145524795760549187848876984780674103116812782182831713215847987 : Int) := by decide +kernel

theorem geometryRow079_jensenBound_denominator_nonzero : (27133740312078666841442775879896045024462676063740773841260944145524795760549187848876984780674103116812782182831713215847987 : Int) ≠ 0 := by decide +kernel

theorem geometryRow079_jensenBound_parse :
    parseRational geometryRow079_jensenBoundText = .ok geometryRowsTyped079.jensenBound :=
  original_rational_fraction_of_chars geometryRow079_jensenBoundNumeratorChars geometryRow079_jensenBoundDenominatorChars
    (72295130845170338754093143846342471581117473855358610617629751676393326159523119675333242375000000000000000000000 : Int) (27133740312078666841442775879896045024462676063740773841260944145524795760549187848876984780674103116812782182831713215847987 : Int)
    geometryRow079_jensenBound_numerator_no_slash geometryRow079_jensenBound_numerator_parse
    geometryRow079_jensenBound_denominator_parse geometryRow079_jensenBound_denominator_nonzero

theorem geometryRow079_jensenBound_read :
    rationalField geometryRowsJson079 "jensen_bound" = .ok geometryRowsTyped079.jensenBound :=
  original_rationalField_of_string geometryRowsJson079 "jensen_bound" geometryRow079_jensenBoundText
    geometryRowsTyped079.jensenBound geometryRow079_jensenBound_field geometryRow079_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_factorMaxima_before"
  err.flush

theorem geometryRow079_factorMaxima_read :
    rationalArrayField geometryRowsJson079 "factor_maxima" = .ok geometryRowsTyped079.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_gapWeightedMeans_before"
  err.flush

theorem geometryRow079_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson079 "gap_weighted_means" = .ok geometryRowsTyped079.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow079_floorChars : List Char := ['2', '1', '1', '0', '9', '5', '4', '9', '6', '2', '2', '3', '9', '9', '1', '2', '0', '2']
noncomputable def geometryRow079_floorText : String := String.ofList geometryRow079_floorChars

theorem geometryRow079_floor_text_read :
    geometryRowsJson079.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow079_floorText := by rfl

theorem geometryRow079_floor_chars_parse :
    SourceJson.intChars geometryRow079_floorChars = some (211095496223991202 : Int) := by decide +kernel

theorem geometryRow079_floor_parse :
    parseInteger geometryRow079_floorText = .ok geometryRowsTyped079.jensenFloorQ96 := by
  simp only [geometryRow079_floorText, parseInteger, String.toList_ofList, geometryRow079_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_079 :
    decodeGeometryRow geometryRowsJson079 = .ok geometryRowsTyped079 :=
  original_geometryRow_of_fields geometryRowsJson079 geometryRowsTyped079 geometryRow079_floorText
    geometryRow079_simplexId_read geometryRow079_vertexIds_read
    geometryRow079_physicalVolume_read geometryRow079_meanGap_read
    geometryRow079_factorMaxima_read geometryRow079_gapWeightedMeans_read
    geometryRow079_jensenBound_read geometryRow079_floor_text_read geometryRow079_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_079_original_decoder_complete"
  err.flush

theorem geometryRow079_shape :
    geometryRowsTyped079.simplexId = 79 ∧
    geometryRowsTyped079.vertexIds.size = 9 ∧ geometryRowsTyped079.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped079.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped079.factorMaxima.size = 10 ∧ geometryRowsTyped079.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock009 : List SourceJson := [geometryRowsJson072, geometryRowsJson073, geometryRowsJson074, geometryRowsJson075, geometryRowsJson076, geometryRowsJson077, geometryRowsJson078, geometryRowsJson079]
noncomputable def geometryRowsTypedBlock009 : List GeometryRow := [geometryRowsTyped072, geometryRowsTyped073, geometryRowsTyped074, geometryRowsTyped075, geometryRowsTyped076, geometryRowsTyped077, geometryRowsTyped078, geometryRowsTyped079]

theorem geometry_Rows_block_009_push_eq (acc : List SourceJson) :
    SimplicesBlock009.blockPush acc = [geometryRowsJson079, geometryRowsJson078, geometryRowsJson077, geometryRowsJson076, geometryRowsJson075, geometryRowsJson074, geometryRowsJson073, geometryRowsJson072] ++ acc := by rfl

theorem geometry_Rows_block_009_reverse (acc : List SourceJson) :
    (SimplicesBlock009.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock009 := by
  rw [geometry_Rows_block_009_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_009 :
    geometryRowsJsonBlock009.mapM decodeGeometryRow = .ok geometryRowsTypedBlock009 := by
  simp only [geometryRowsJsonBlock009, geometryRowsTypedBlock009, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_072, decode_geometry_Rows_073, decode_geometry_Rows_074, decode_geometry_Rows_075, decode_geometry_Rows_076, decode_geometry_Rows_077, decode_geometry_Rows_078, decode_geometry_Rows_079]
  rfl

theorem geometry_Rows_block_009_length : geometryRowsTypedBlock009.length = 8 := by rfl

#print axioms geometryRow072_simplexId_read
#print axioms geometryRow072_vertexIds_read
#print axioms geometryRow072_physicalVolume_field
#print axioms geometryRow072_physicalVolume_numerator_no_slash
#print axioms geometryRow072_physicalVolume_numerator_parse
#print axioms geometryRow072_physicalVolume_denominator_parse
#print axioms geometryRow072_physicalVolume_denominator_nonzero
#print axioms geometryRow072_physicalVolume_parse
#print axioms geometryRow072_physicalVolume_read
#print axioms geometryRow072_meanGap_field
#print axioms geometryRow072_meanGap_numerator_no_slash
#print axioms geometryRow072_meanGap_numerator_parse
#print axioms geometryRow072_meanGap_denominator_parse
#print axioms geometryRow072_meanGap_denominator_nonzero
#print axioms geometryRow072_meanGap_parse
#print axioms geometryRow072_meanGap_read
#print axioms geometryRow072_jensenBound_field
#print axioms geometryRow072_jensenBound_numerator_no_slash
#print axioms geometryRow072_jensenBound_numerator_parse
#print axioms geometryRow072_jensenBound_denominator_parse
#print axioms geometryRow072_jensenBound_denominator_nonzero
#print axioms geometryRow072_jensenBound_parse
#print axioms geometryRow072_jensenBound_read
#print axioms geometryRow072_factorMaxima_read
#print axioms geometryRow072_gapWeightedMeans_read
#print axioms geometryRow072_floor_text_read
#print axioms geometryRow072_floor_chars_parse
#print axioms geometryRow072_floor_parse
#print axioms decode_geometry_Rows_072
#print axioms geometryRow072_shape
#print axioms geometryRow073_simplexId_read
#print axioms geometryRow073_vertexIds_read
#print axioms geometryRow073_physicalVolume_field
#print axioms geometryRow073_physicalVolume_numerator_no_slash
#print axioms geometryRow073_physicalVolume_numerator_parse
#print axioms geometryRow073_physicalVolume_denominator_parse
#print axioms geometryRow073_physicalVolume_denominator_nonzero
#print axioms geometryRow073_physicalVolume_parse
#print axioms geometryRow073_physicalVolume_read
#print axioms geometryRow073_meanGap_field
#print axioms geometryRow073_meanGap_numerator_no_slash
#print axioms geometryRow073_meanGap_numerator_parse
#print axioms geometryRow073_meanGap_denominator_parse
#print axioms geometryRow073_meanGap_denominator_nonzero
#print axioms geometryRow073_meanGap_parse
#print axioms geometryRow073_meanGap_read
#print axioms geometryRow073_jensenBound_field
#print axioms geometryRow073_jensenBound_numerator_no_slash
#print axioms geometryRow073_jensenBound_numerator_parse
#print axioms geometryRow073_jensenBound_denominator_parse
#print axioms geometryRow073_jensenBound_denominator_nonzero
#print axioms geometryRow073_jensenBound_parse
#print axioms geometryRow073_jensenBound_read
#print axioms geometryRow073_factorMaxima_read
#print axioms geometryRow073_gapWeightedMeans_read
#print axioms geometryRow073_floor_text_read
#print axioms geometryRow073_floor_chars_parse
#print axioms geometryRow073_floor_parse
#print axioms decode_geometry_Rows_073
#print axioms geometryRow073_shape
#print axioms geometryRow074_simplexId_read
#print axioms geometryRow074_vertexIds_read
#print axioms geometryRow074_physicalVolume_field
#print axioms geometryRow074_physicalVolume_numerator_no_slash
#print axioms geometryRow074_physicalVolume_numerator_parse
#print axioms geometryRow074_physicalVolume_denominator_parse
#print axioms geometryRow074_physicalVolume_denominator_nonzero
#print axioms geometryRow074_physicalVolume_parse
#print axioms geometryRow074_physicalVolume_read
#print axioms geometryRow074_meanGap_field
#print axioms geometryRow074_meanGap_numerator_no_slash
#print axioms geometryRow074_meanGap_numerator_parse
#print axioms geometryRow074_meanGap_denominator_parse
#print axioms geometryRow074_meanGap_denominator_nonzero
#print axioms geometryRow074_meanGap_parse
#print axioms geometryRow074_meanGap_read
#print axioms geometryRow074_jensenBound_field
#print axioms geometryRow074_jensenBound_numerator_no_slash
#print axioms geometryRow074_jensenBound_numerator_parse
#print axioms geometryRow074_jensenBound_denominator_parse
#print axioms geometryRow074_jensenBound_denominator_nonzero
#print axioms geometryRow074_jensenBound_parse
#print axioms geometryRow074_jensenBound_read
#print axioms geometryRow074_factorMaxima_read
#print axioms geometryRow074_gapWeightedMeans_read
#print axioms geometryRow074_floor_text_read
#print axioms geometryRow074_floor_chars_parse
#print axioms geometryRow074_floor_parse
#print axioms decode_geometry_Rows_074
#print axioms geometryRow074_shape
#print axioms geometryRow075_simplexId_read
#print axioms geometryRow075_vertexIds_read
#print axioms geometryRow075_physicalVolume_field
#print axioms geometryRow075_physicalVolume_numerator_no_slash
#print axioms geometryRow075_physicalVolume_numerator_parse
#print axioms geometryRow075_physicalVolume_denominator_parse
#print axioms geometryRow075_physicalVolume_denominator_nonzero
#print axioms geometryRow075_physicalVolume_parse
#print axioms geometryRow075_physicalVolume_read
#print axioms geometryRow075_meanGap_field
#print axioms geometryRow075_meanGap_numerator_no_slash
#print axioms geometryRow075_meanGap_numerator_parse
#print axioms geometryRow075_meanGap_denominator_parse
#print axioms geometryRow075_meanGap_denominator_nonzero
#print axioms geometryRow075_meanGap_parse
#print axioms geometryRow075_meanGap_read
#print axioms geometryRow075_jensenBound_field
#print axioms geometryRow075_jensenBound_numerator_no_slash
#print axioms geometryRow075_jensenBound_numerator_parse
#print axioms geometryRow075_jensenBound_denominator_parse
#print axioms geometryRow075_jensenBound_denominator_nonzero
#print axioms geometryRow075_jensenBound_parse
#print axioms geometryRow075_jensenBound_read
#print axioms geometryRow075_factorMaxima_read
#print axioms geometryRow075_gapWeightedMeans_read
#print axioms geometryRow075_floor_text_read
#print axioms geometryRow075_floor_chars_parse
#print axioms geometryRow075_floor_parse
#print axioms decode_geometry_Rows_075
#print axioms geometryRow075_shape
#print axioms geometryRow076_simplexId_read
#print axioms geometryRow076_vertexIds_read
#print axioms geometryRow076_physicalVolume_field
#print axioms geometryRow076_physicalVolume_numerator_no_slash
#print axioms geometryRow076_physicalVolume_numerator_parse
#print axioms geometryRow076_physicalVolume_denominator_parse
#print axioms geometryRow076_physicalVolume_denominator_nonzero
#print axioms geometryRow076_physicalVolume_parse
#print axioms geometryRow076_physicalVolume_read
#print axioms geometryRow076_meanGap_field
#print axioms geometryRow076_meanGap_numerator_no_slash
#print axioms geometryRow076_meanGap_numerator_parse
#print axioms geometryRow076_meanGap_denominator_parse
#print axioms geometryRow076_meanGap_denominator_nonzero
#print axioms geometryRow076_meanGap_parse
#print axioms geometryRow076_meanGap_read
#print axioms geometryRow076_jensenBound_field
#print axioms geometryRow076_jensenBound_numerator_no_slash
#print axioms geometryRow076_jensenBound_numerator_parse
#print axioms geometryRow076_jensenBound_denominator_parse
#print axioms geometryRow076_jensenBound_denominator_nonzero
#print axioms geometryRow076_jensenBound_parse
#print axioms geometryRow076_jensenBound_read
#print axioms geometryRow076_factorMaxima_read
#print axioms geometryRow076_gapWeightedMeans_read
#print axioms geometryRow076_floor_text_read
#print axioms geometryRow076_floor_chars_parse
#print axioms geometryRow076_floor_parse
#print axioms decode_geometry_Rows_076
#print axioms geometryRow076_shape
#print axioms geometryRow077_simplexId_read
#print axioms geometryRow077_vertexIds_read
#print axioms geometryRow077_physicalVolume_field
#print axioms geometryRow077_physicalVolume_numerator_no_slash
#print axioms geometryRow077_physicalVolume_numerator_parse
#print axioms geometryRow077_physicalVolume_denominator_parse
#print axioms geometryRow077_physicalVolume_denominator_nonzero
#print axioms geometryRow077_physicalVolume_parse
#print axioms geometryRow077_physicalVolume_read
#print axioms geometryRow077_meanGap_field
#print axioms geometryRow077_meanGap_numerator_no_slash
#print axioms geometryRow077_meanGap_numerator_parse
#print axioms geometryRow077_meanGap_denominator_parse
#print axioms geometryRow077_meanGap_denominator_nonzero
#print axioms geometryRow077_meanGap_parse
#print axioms geometryRow077_meanGap_read
#print axioms geometryRow077_jensenBound_field
#print axioms geometryRow077_jensenBound_numerator_no_slash
#print axioms geometryRow077_jensenBound_numerator_parse
#print axioms geometryRow077_jensenBound_denominator_parse
#print axioms geometryRow077_jensenBound_denominator_nonzero
#print axioms geometryRow077_jensenBound_parse
#print axioms geometryRow077_jensenBound_read
#print axioms geometryRow077_factorMaxima_read
#print axioms geometryRow077_gapWeightedMeans_read
#print axioms geometryRow077_floor_text_read
#print axioms geometryRow077_floor_chars_parse
#print axioms geometryRow077_floor_parse
#print axioms decode_geometry_Rows_077
#print axioms geometryRow077_shape
#print axioms geometryRow078_simplexId_read
#print axioms geometryRow078_vertexIds_read
#print axioms geometryRow078_physicalVolume_field
#print axioms geometryRow078_physicalVolume_numerator_no_slash
#print axioms geometryRow078_physicalVolume_numerator_parse
#print axioms geometryRow078_physicalVolume_denominator_parse
#print axioms geometryRow078_physicalVolume_denominator_nonzero
#print axioms geometryRow078_physicalVolume_parse
#print axioms geometryRow078_physicalVolume_read
#print axioms geometryRow078_meanGap_field
#print axioms geometryRow078_meanGap_numerator_no_slash
#print axioms geometryRow078_meanGap_numerator_parse
#print axioms geometryRow078_meanGap_denominator_parse
#print axioms geometryRow078_meanGap_denominator_nonzero
#print axioms geometryRow078_meanGap_parse
#print axioms geometryRow078_meanGap_read
#print axioms geometryRow078_jensenBound_field
#print axioms geometryRow078_jensenBound_numerator_no_slash
#print axioms geometryRow078_jensenBound_numerator_parse
#print axioms geometryRow078_jensenBound_denominator_parse
#print axioms geometryRow078_jensenBound_denominator_nonzero
#print axioms geometryRow078_jensenBound_parse
#print axioms geometryRow078_jensenBound_read
#print axioms geometryRow078_factorMaxima_read
#print axioms geometryRow078_gapWeightedMeans_read
#print axioms geometryRow078_floor_text_read
#print axioms geometryRow078_floor_chars_parse
#print axioms geometryRow078_floor_parse
#print axioms decode_geometry_Rows_078
#print axioms geometryRow078_shape
#print axioms geometryRow079_simplexId_read
#print axioms geometryRow079_vertexIds_read
#print axioms geometryRow079_physicalVolume_field
#print axioms geometryRow079_physicalVolume_numerator_no_slash
#print axioms geometryRow079_physicalVolume_numerator_parse
#print axioms geometryRow079_physicalVolume_denominator_parse
#print axioms geometryRow079_physicalVolume_denominator_nonzero
#print axioms geometryRow079_physicalVolume_parse
#print axioms geometryRow079_physicalVolume_read
#print axioms geometryRow079_meanGap_field
#print axioms geometryRow079_meanGap_numerator_no_slash
#print axioms geometryRow079_meanGap_numerator_parse
#print axioms geometryRow079_meanGap_denominator_parse
#print axioms geometryRow079_meanGap_denominator_nonzero
#print axioms geometryRow079_meanGap_parse
#print axioms geometryRow079_meanGap_read
#print axioms geometryRow079_jensenBound_field
#print axioms geometryRow079_jensenBound_numerator_no_slash
#print axioms geometryRow079_jensenBound_numerator_parse
#print axioms geometryRow079_jensenBound_denominator_parse
#print axioms geometryRow079_jensenBound_denominator_nonzero
#print axioms geometryRow079_jensenBound_parse
#print axioms geometryRow079_jensenBound_read
#print axioms geometryRow079_factorMaxima_read
#print axioms geometryRow079_gapWeightedMeans_read
#print axioms geometryRow079_floor_text_read
#print axioms geometryRow079_floor_chars_parse
#print axioms geometryRow079_floor_parse
#print axioms decode_geometry_Rows_079
#print axioms geometryRow079_shape
#print axioms geometry_Rows_block_009_push_eq
#print axioms geometry_Rows_block_009_reverse
#print axioms decode_geometry_Rows_block_009
#print axioms geometry_Rows_block_009_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
