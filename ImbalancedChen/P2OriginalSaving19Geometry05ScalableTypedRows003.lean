import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableSimplicesBlock003

/-! Local typed certificates for original cell 05, rows 24 through 31.
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

noncomputable def geometryRowsJson024 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped024 : GeometryRow :=
  { simplexId := 24,
    vertexIds := #[27, 25, 23, 21, 19, 7, 6, 4, 0],
    physicalVolume := ((920166393502259362664872262495985613 : ℚ) / (20978384157000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2999973 : ℚ) / (30500000 : ℚ)), ((2999973 : ℚ) / (30500000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ))],
    gapWeightedMeans := #[((57823222993271633 : ℚ) / (644603299200000000 : ℚ)), ((7269198906105691 : ℚ) / (80575412400000000 : ℚ)), ((7861164877911503 : ℚ) / (64460329920000000 : ℚ)), ((14860421086117751 : ℚ) / (161150824800000000 : ℚ)), ((14246881463792989 : ℚ) / (161150824800000000 : ℚ)), ((2305607949693179 : ℚ) / (32230164960000000 : ℚ)), ((12224850397745597 : ℚ) / (322301649600000000 : ℚ)), ((3514528540102171 : ℚ) / (107433883200000000 : ℚ)), ((3386408388683611 : ℚ) / (107433883200000000 : ℚ)), ((826332923016259 : ℚ) / (26858470800000000 : ℚ))],
    jensenBound := ((1271558828283914520026750317031363723278947476450868901518531886951040983615161033051250481619965930269664083186450169856000000000000000000000000 : ℚ) / (17628869807315514660091523959850676226143319310919134768767100260934206841338674061273198711443205453796319220541315940608352782050318457814129809421982265257 : ℚ)),
    jensenFloorQ96 := (5714675449694439 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_simplexId_before"
  err.flush

theorem geometryRow024_simplexId_read :
    geometryRowsJson024.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped024.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_vertexIds_before"
  err.flush

theorem geometryRow024_vertexIds_read :
    geometryRowsJson024.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped024.vertexIds := by decide +kernel

noncomputable def geometryRow024_physicalVolumeNumeratorChars : List Char := ['9', '2', '0', '1', '6', '6', '3', '9', '3', '5', '0', '2', '2', '5', '9', '3', '6', '2', '6', '6', '4', '8', '7', '2', '2', '6', '2', '4', '9', '5', '9', '8', '5', '6', '1', '3']
noncomputable def geometryRow024_physicalVolumeDenominatorChars : List Char := ['2', '0', '9', '7', '8', '3', '8', '4', '1', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_physicalVolumeText : String := String.ofList (geometryRow024_physicalVolumeNumeratorChars ++ '/' :: geometryRow024_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_physicalVolume_before_field"
  err.flush

theorem geometryRow024_physicalVolume_field :
    geometryRowsJson024.getObjVal? "physical_volume" = .ok (.str geometryRow024_physicalVolumeText) := by rfl

theorem geometryRow024_physicalVolume_numerator_no_slash :
    geometryRow024_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow024_physicalVolumeNumeratorChars = some (920166393502259362664872262495985613 : Int) := by decide +kernel

theorem geometryRow024_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow024_physicalVolumeDenominatorChars = some (20978384157000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow024_physicalVolume_denominator_nonzero : (20978384157000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_physicalVolume_parse :
    parseRational geometryRow024_physicalVolumeText = .ok geometryRowsTyped024.physicalVolume :=
  original_rational_fraction_of_chars geometryRow024_physicalVolumeNumeratorChars geometryRow024_physicalVolumeDenominatorChars
    (920166393502259362664872262495985613 : Int) (20978384157000000000000000000000000000000000000000000000000 : Int)
    geometryRow024_physicalVolume_numerator_no_slash geometryRow024_physicalVolume_numerator_parse
    geometryRow024_physicalVolume_denominator_parse geometryRow024_physicalVolume_denominator_nonzero

theorem geometryRow024_physicalVolume_read :
    rationalField geometryRowsJson024 "physical_volume" = .ok geometryRowsTyped024.physicalVolume :=
  original_rationalField_of_string geometryRowsJson024 "physical_volume" geometryRow024_physicalVolumeText
    geometryRowsTyped024.physicalVolume geometryRow024_physicalVolume_field geometryRow024_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_physicalVolume_complete"
  err.flush

noncomputable def geometryRow024_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow024_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_meanGapText : String := String.ofList (geometryRow024_meanGapNumeratorChars ++ '/' :: geometryRow024_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_meanGap_before_field"
  err.flush

theorem geometryRow024_meanGap_field :
    geometryRowsJson024.getObjVal? "mean_gap" = .ok (.str geometryRow024_meanGapText) := by rfl

theorem geometryRow024_meanGap_numerator_no_slash :
    geometryRow024_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_meanGap_numerator_parse :
    SourceJson.intChars geometryRow024_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow024_meanGap_denominator_parse :
    SourceJson.intChars geometryRow024_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow024_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_meanGap_parse :
    parseRational geometryRow024_meanGapText = .ok geometryRowsTyped024.meanGap :=
  original_rational_fraction_of_chars geometryRow024_meanGapNumeratorChars geometryRow024_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow024_meanGap_numerator_no_slash geometryRow024_meanGap_numerator_parse
    geometryRow024_meanGap_denominator_parse geometryRow024_meanGap_denominator_nonzero

theorem geometryRow024_meanGap_read :
    rationalField geometryRowsJson024 "mean_gap" = .ok geometryRowsTyped024.meanGap :=
  original_rationalField_of_string geometryRowsJson024 "mean_gap" geometryRow024_meanGapText
    geometryRowsTyped024.meanGap geometryRow024_meanGap_field geometryRow024_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_meanGap_complete"
  err.flush

noncomputable def geometryRow024_jensenBoundNumeratorChars : List Char := ['1', '2', '7', '1', '5', '5', '8', '8', '2', '8', '2', '8', '3', '9', '1', '4', '5', '2', '0', '0', '2', '6', '7', '5', '0', '3', '1', '7', '0', '3', '1', '3', '6', '3', '7', '2', '3', '2', '7', '8', '9', '4', '7', '4', '7', '6', '4', '5', '0', '8', '6', '8', '9', '0', '1', '5', '1', '8', '5', '3', '1', '8', '8', '6', '9', '5', '1', '0', '4', '0', '9', '8', '3', '6', '1', '5', '1', '6', '1', '0', '3', '3', '0', '5', '1', '2', '5', '0', '4', '8', '1', '6', '1', '9', '9', '6', '5', '9', '3', '0', '2', '6', '9', '6', '6', '4', '0', '8', '3', '1', '8', '6', '4', '5', '0', '1', '6', '9', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_jensenBoundDenominatorChars : List Char := ['1', '7', '6', '2', '8', '8', '6', '9', '8', '0', '7', '3', '1', '5', '5', '1', '4', '6', '6', '0', '0', '9', '1', '5', '2', '3', '9', '5', '9', '8', '5', '0', '6', '7', '6', '2', '2', '6', '1', '4', '3', '3', '1', '9', '3', '1', '0', '9', '1', '9', '1', '3', '4', '7', '6', '8', '7', '6', '7', '1', '0', '0', '2', '6', '0', '9', '3', '4', '2', '0', '6', '8', '4', '1', '3', '3', '8', '6', '7', '4', '0', '6', '1', '2', '7', '3', '1', '9', '8', '7', '1', '1', '4', '4', '3', '2', '0', '5', '4', '5', '3', '7', '9', '6', '3', '1', '9', '2', '2', '0', '5', '4', '1', '3', '1', '5', '9', '4', '0', '6', '0', '8', '3', '5', '2', '7', '8', '2', '0', '5', '0', '3', '1', '8', '4', '5', '7', '8', '1', '4', '1', '2', '9', '8', '0', '9', '4', '2', '1', '9', '8', '2', '2', '6', '5', '2', '5', '7']
noncomputable def geometryRow024_jensenBoundText : String := String.ofList (geometryRow024_jensenBoundNumeratorChars ++ '/' :: geometryRow024_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_jensenBound_before_field"
  err.flush

theorem geometryRow024_jensenBound_field :
    geometryRowsJson024.getObjVal? "jensen_bound" = .ok (.str geometryRow024_jensenBoundText) := by rfl

theorem geometryRow024_jensenBound_numerator_no_slash :
    geometryRow024_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow024_jensenBoundNumeratorChars = some (1271558828283914520026750317031363723278947476450868901518531886951040983615161033051250481619965930269664083186450169856000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow024_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow024_jensenBoundDenominatorChars = some (17628869807315514660091523959850676226143319310919134768767100260934206841338674061273198711443205453796319220541315940608352782050318457814129809421982265257 : Int) := by decide +kernel

theorem geometryRow024_jensenBound_denominator_nonzero : (17628869807315514660091523959850676226143319310919134768767100260934206841338674061273198711443205453796319220541315940608352782050318457814129809421982265257 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_jensenBound_parse :
    parseRational geometryRow024_jensenBoundText = .ok geometryRowsTyped024.jensenBound :=
  original_rational_fraction_of_chars geometryRow024_jensenBoundNumeratorChars geometryRow024_jensenBoundDenominatorChars
    (1271558828283914520026750317031363723278947476450868901518531886951040983615161033051250481619965930269664083186450169856000000000000000000000000 : Int) (17628869807315514660091523959850676226143319310919134768767100260934206841338674061273198711443205453796319220541315940608352782050318457814129809421982265257 : Int)
    geometryRow024_jensenBound_numerator_no_slash geometryRow024_jensenBound_numerator_parse
    geometryRow024_jensenBound_denominator_parse geometryRow024_jensenBound_denominator_nonzero

theorem geometryRow024_jensenBound_read :
    rationalField geometryRowsJson024 "jensen_bound" = .ok geometryRowsTyped024.jensenBound :=
  original_rationalField_of_string geometryRowsJson024 "jensen_bound" geometryRow024_jensenBoundText
    geometryRowsTyped024.jensenBound geometryRow024_jensenBound_field geometryRow024_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_factorMaxima_before"
  err.flush

theorem geometryRow024_factorMaxima_read :
    rationalArrayField geometryRowsJson024 "factor_maxima" = .ok geometryRowsTyped024.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_gapWeightedMeans_before"
  err.flush

theorem geometryRow024_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson024 "gap_weighted_means" = .ok geometryRowsTyped024.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow024_floorChars : List Char := ['5', '7', '1', '4', '6', '7', '5', '4', '4', '9', '6', '9', '4', '4', '3', '9']
noncomputable def geometryRow024_floorText : String := String.ofList geometryRow024_floorChars

theorem geometryRow024_floor_text_read :
    geometryRowsJson024.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow024_floorText := by rfl

theorem geometryRow024_floor_chars_parse :
    SourceJson.intChars geometryRow024_floorChars = some (5714675449694439 : Int) := by decide +kernel

theorem geometryRow024_floor_parse :
    parseInteger geometryRow024_floorText = .ok geometryRowsTyped024.jensenFloorQ96 := by
  simp only [geometryRow024_floorText, parseInteger, String.toList_ofList, geometryRow024_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_024 :
    decodeGeometryRow geometryRowsJson024 = .ok geometryRowsTyped024 :=
  original_geometryRow_of_fields geometryRowsJson024 geometryRowsTyped024 geometryRow024_floorText
    geometryRow024_simplexId_read geometryRow024_vertexIds_read
    geometryRow024_physicalVolume_read geometryRow024_meanGap_read
    geometryRow024_factorMaxima_read geometryRow024_gapWeightedMeans_read
    geometryRow024_jensenBound_read geometryRow024_floor_text_read geometryRow024_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_024_original_decoder_complete"
  err.flush

theorem geometryRow024_shape :
    geometryRowsTyped024.simplexId = 24 ∧
    geometryRowsTyped024.vertexIds.size = 9 ∧ geometryRowsTyped024.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped024.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped024.factorMaxima.size = 10 ∧ geometryRowsTyped024.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson025 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped025 : GeometryRow :=
  { simplexId := 25,
    vertexIds := #[27, 25, 23, 21, 19, 17, 5, 1, 0],
    physicalVolume := ((8856330976831278727423796238013 : ℚ) / (1551235682812500000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((12984403 : ℚ) / (136000000 : ℚ)), ((3328101 : ℚ) / (34000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((2328113 : ℚ) / (68000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ))],
    gapWeightedMeans := #[((18677345631107 : ℚ) / (211843800000000 : ℚ)), ((9389764711321 : ℚ) / (105921900000000 : ℚ)), ((2596297431557 : ℚ) / (21184380000000 : ℚ)), ((9880434162733 : ℚ) / (105921900000000 : ℚ)), ((9567355318697 : ℚ) / (105921900000000 : ℚ)), ((379045248133 : ℚ) / (5296095000000 : ℚ)), ((520059228811 : ℚ) / (13240237500000 : ℚ)), ((23096523383 : ℚ) / (735568750000 : ℚ)), ((1067823271589 : ℚ) / (35307300000000 : ℚ)), ((1067816210129 : ℚ) / (35307300000000 : ℚ))],
    jensenBound := ((190778636219082637582353017522420178475070007241704865088420835446908287756086371815000000000000000000000 : ℚ) / (20313554491083582430515786163404134707073623187109181118493563674270605369568612516080424146059108659987721579029086862061 : ℚ)),
    jensenFloorQ96 := (744086457210 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_simplexId_before"
  err.flush

theorem geometryRow025_simplexId_read :
    geometryRowsJson025.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped025.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_vertexIds_before"
  err.flush

theorem geometryRow025_vertexIds_read :
    geometryRowsJson025.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped025.vertexIds := by decide +kernel

noncomputable def geometryRow025_physicalVolumeNumeratorChars : List Char := ['8', '8', '5', '6', '3', '3', '0', '9', '7', '6', '8', '3', '1', '2', '7', '8', '7', '2', '7', '4', '2', '3', '7', '9', '6', '2', '3', '8', '0', '1', '3']
noncomputable def geometryRow025_physicalVolumeDenominatorChars : List Char := ['1', '5', '5', '1', '2', '3', '5', '6', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_physicalVolumeText : String := String.ofList (geometryRow025_physicalVolumeNumeratorChars ++ '/' :: geometryRow025_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_physicalVolume_before_field"
  err.flush

theorem geometryRow025_physicalVolume_field :
    geometryRowsJson025.getObjVal? "physical_volume" = .ok (.str geometryRow025_physicalVolumeText) := by rfl

theorem geometryRow025_physicalVolume_numerator_no_slash :
    geometryRow025_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow025_physicalVolumeNumeratorChars = some (8856330976831278727423796238013 : Int) := by decide +kernel

theorem geometryRow025_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow025_physicalVolumeDenominatorChars = some (1551235682812500000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow025_physicalVolume_denominator_nonzero : (1551235682812500000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_physicalVolume_parse :
    parseRational geometryRow025_physicalVolumeText = .ok geometryRowsTyped025.physicalVolume :=
  original_rational_fraction_of_chars geometryRow025_physicalVolumeNumeratorChars geometryRow025_physicalVolumeDenominatorChars
    (8856330976831278727423796238013 : Int) (1551235682812500000000000000000000000000000000000000000000 : Int)
    geometryRow025_physicalVolume_numerator_no_slash geometryRow025_physicalVolume_numerator_parse
    geometryRow025_physicalVolume_denominator_parse geometryRow025_physicalVolume_denominator_nonzero

theorem geometryRow025_physicalVolume_read :
    rationalField geometryRowsJson025 "physical_volume" = .ok geometryRowsTyped025.physicalVolume :=
  original_rationalField_of_string geometryRowsJson025 "physical_volume" geometryRow025_physicalVolumeText
    geometryRowsTyped025.physicalVolume geometryRow025_physicalVolume_field geometryRow025_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_physicalVolume_complete"
  err.flush

noncomputable def geometryRow025_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow025_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_meanGapText : String := String.ofList (geometryRow025_meanGapNumeratorChars ++ '/' :: geometryRow025_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_meanGap_before_field"
  err.flush

theorem geometryRow025_meanGap_field :
    geometryRowsJson025.getObjVal? "mean_gap" = .ok (.str geometryRow025_meanGapText) := by rfl

theorem geometryRow025_meanGap_numerator_no_slash :
    geometryRow025_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_meanGap_numerator_parse :
    SourceJson.intChars geometryRow025_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow025_meanGap_denominator_parse :
    SourceJson.intChars geometryRow025_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow025_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_meanGap_parse :
    parseRational geometryRow025_meanGapText = .ok geometryRowsTyped025.meanGap :=
  original_rational_fraction_of_chars geometryRow025_meanGapNumeratorChars geometryRow025_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow025_meanGap_numerator_no_slash geometryRow025_meanGap_numerator_parse
    geometryRow025_meanGap_denominator_parse geometryRow025_meanGap_denominator_nonzero

theorem geometryRow025_meanGap_read :
    rationalField geometryRowsJson025 "mean_gap" = .ok geometryRowsTyped025.meanGap :=
  original_rationalField_of_string geometryRowsJson025 "mean_gap" geometryRow025_meanGapText
    geometryRowsTyped025.meanGap geometryRow025_meanGap_field geometryRow025_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_meanGap_complete"
  err.flush

noncomputable def geometryRow025_jensenBoundNumeratorChars : List Char := ['1', '9', '0', '7', '7', '8', '6', '3', '6', '2', '1', '9', '0', '8', '2', '6', '3', '7', '5', '8', '2', '3', '5', '3', '0', '1', '7', '5', '2', '2', '4', '2', '0', '1', '7', '8', '4', '7', '5', '0', '7', '0', '0', '0', '7', '2', '4', '1', '7', '0', '4', '8', '6', '5', '0', '8', '8', '4', '2', '0', '8', '3', '5', '4', '4', '6', '9', '0', '8', '2', '8', '7', '7', '5', '6', '0', '8', '6', '3', '7', '1', '8', '1', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_jensenBoundDenominatorChars : List Char := ['2', '0', '3', '1', '3', '5', '5', '4', '4', '9', '1', '0', '8', '3', '5', '8', '2', '4', '3', '0', '5', '1', '5', '7', '8', '6', '1', '6', '3', '4', '0', '4', '1', '3', '4', '7', '0', '7', '0', '7', '3', '6', '2', '3', '1', '8', '7', '1', '0', '9', '1', '8', '1', '1', '1', '8', '4', '9', '3', '5', '6', '3', '6', '7', '4', '2', '7', '0', '6', '0', '5', '3', '6', '9', '5', '6', '8', '6', '1', '2', '5', '1', '6', '0', '8', '0', '4', '2', '4', '1', '4', '6', '0', '5', '9', '1', '0', '8', '6', '5', '9', '9', '8', '7', '7', '2', '1', '5', '7', '9', '0', '2', '9', '0', '8', '6', '8', '6', '2', '0', '6', '1']
noncomputable def geometryRow025_jensenBoundText : String := String.ofList (geometryRow025_jensenBoundNumeratorChars ++ '/' :: geometryRow025_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_jensenBound_before_field"
  err.flush

theorem geometryRow025_jensenBound_field :
    geometryRowsJson025.getObjVal? "jensen_bound" = .ok (.str geometryRow025_jensenBoundText) := by rfl

theorem geometryRow025_jensenBound_numerator_no_slash :
    geometryRow025_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow025_jensenBoundNumeratorChars = some (190778636219082637582353017522420178475070007241704865088420835446908287756086371815000000000000000000000 : Int) := by decide +kernel

theorem geometryRow025_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow025_jensenBoundDenominatorChars = some (20313554491083582430515786163404134707073623187109181118493563674270605369568612516080424146059108659987721579029086862061 : Int) := by decide +kernel

theorem geometryRow025_jensenBound_denominator_nonzero : (20313554491083582430515786163404134707073623187109181118493563674270605369568612516080424146059108659987721579029086862061 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_jensenBound_parse :
    parseRational geometryRow025_jensenBoundText = .ok geometryRowsTyped025.jensenBound :=
  original_rational_fraction_of_chars geometryRow025_jensenBoundNumeratorChars geometryRow025_jensenBoundDenominatorChars
    (190778636219082637582353017522420178475070007241704865088420835446908287756086371815000000000000000000000 : Int) (20313554491083582430515786163404134707073623187109181118493563674270605369568612516080424146059108659987721579029086862061 : Int)
    geometryRow025_jensenBound_numerator_no_slash geometryRow025_jensenBound_numerator_parse
    geometryRow025_jensenBound_denominator_parse geometryRow025_jensenBound_denominator_nonzero

theorem geometryRow025_jensenBound_read :
    rationalField geometryRowsJson025 "jensen_bound" = .ok geometryRowsTyped025.jensenBound :=
  original_rationalField_of_string geometryRowsJson025 "jensen_bound" geometryRow025_jensenBoundText
    geometryRowsTyped025.jensenBound geometryRow025_jensenBound_field geometryRow025_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_factorMaxima_before"
  err.flush

theorem geometryRow025_factorMaxima_read :
    rationalArrayField geometryRowsJson025 "factor_maxima" = .ok geometryRowsTyped025.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_gapWeightedMeans_before"
  err.flush

theorem geometryRow025_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson025 "gap_weighted_means" = .ok geometryRowsTyped025.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow025_floorChars : List Char := ['7', '4', '4', '0', '8', '6', '4', '5', '7', '2', '1', '0']
noncomputable def geometryRow025_floorText : String := String.ofList geometryRow025_floorChars

theorem geometryRow025_floor_text_read :
    geometryRowsJson025.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow025_floorText := by rfl

theorem geometryRow025_floor_chars_parse :
    SourceJson.intChars geometryRow025_floorChars = some (744086457210 : Int) := by decide +kernel

theorem geometryRow025_floor_parse :
    parseInteger geometryRow025_floorText = .ok geometryRowsTyped025.jensenFloorQ96 := by
  simp only [geometryRow025_floorText, parseInteger, String.toList_ofList, geometryRow025_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_025 :
    decodeGeometryRow geometryRowsJson025 = .ok geometryRowsTyped025 :=
  original_geometryRow_of_fields geometryRowsJson025 geometryRowsTyped025 geometryRow025_floorText
    geometryRow025_simplexId_read geometryRow025_vertexIds_read
    geometryRow025_physicalVolume_read geometryRow025_meanGap_read
    geometryRow025_factorMaxima_read geometryRow025_gapWeightedMeans_read
    geometryRow025_jensenBound_read geometryRow025_floor_text_read geometryRow025_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_025_original_decoder_complete"
  err.flush

theorem geometryRow025_shape :
    geometryRowsTyped025.simplexId = 25 ∧
    geometryRowsTyped025.vertexIds.size = 9 ∧ geometryRowsTyped025.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped025.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped025.factorMaxima.size = 10 ∧ geometryRowsTyped025.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson026 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped026 : GeometryRow :=
  { simplexId := 26,
    vertexIds := #[27, 25, 23, 21, 19, 17, 5, 4, 0],
    physicalVolume := ((968720252589769422775974500218167343 : ℚ) / (66186055800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((10824169 : ℚ) / (19584000000 : ℚ)),
    factorMaxima := #[((12984403 : ℚ) / (136000000 : ℚ)), ((3328101 : ℚ) / (34000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((2328113 : ℚ) / (68000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ))],
    gapWeightedMeans := #[((3233443802728375987673 : ℚ) / (36688529484835200000000 : ℚ)), ((407603423098557677641 : ℚ) / (4586066185604400000000 : ℚ)), ((90086203666396927627 : ℚ) / (733770589696704000000 : ℚ)), ((861685111142221470011 : ℚ) / (9172132371208800000000 : ℚ)), ((828116759262248566129 : ℚ) / (9172132371208800000000 : ℚ)), ((129929111803360168979 : ℚ) / (1834426474241760000000 : ℚ)), ((702278591091427676237 : ℚ) / (18344264742417600000000 : ℚ)), ((193546960711685906491 : ℚ) / (6114754914139200000000 : ℚ)), ((186986336999124526211 : ℚ) / (6114754914139200000000 : ℚ)), ((46350428330420876609 : ℚ) / (1528688728534800000000 : ℚ))],
    jensenBound := ((58768105657991311212438177816293718510088863753698307646828281306850686802001401108843615437714662646392145170836885999027703523665357486107026094963805451740765742956544000000000000000000000 : ℚ) / (1178894071927935359659977472890025312113863708964016793744345322795652928248348973711651069069042638387415005913784447264833184370878019073696096084978592231027793511090498325204736501527002850780856877933 : ℚ)),
    jensenFloorQ96 := (3949539773418603 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_simplexId_before"
  err.flush

theorem geometryRow026_simplexId_read :
    geometryRowsJson026.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped026.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_vertexIds_before"
  err.flush

theorem geometryRow026_vertexIds_read :
    geometryRowsJson026.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped026.vertexIds := by decide +kernel

noncomputable def geometryRow026_physicalVolumeNumeratorChars : List Char := ['9', '6', '8', '7', '2', '0', '2', '5', '2', '5', '8', '9', '7', '6', '9', '4', '2', '2', '7', '7', '5', '9', '7', '4', '5', '0', '0', '2', '1', '8', '1', '6', '7', '3', '4', '3']
noncomputable def geometryRow026_physicalVolumeDenominatorChars : List Char := ['6', '6', '1', '8', '6', '0', '5', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow026_physicalVolumeText : String := String.ofList (geometryRow026_physicalVolumeNumeratorChars ++ '/' :: geometryRow026_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_physicalVolume_before_field"
  err.flush

theorem geometryRow026_physicalVolume_field :
    geometryRowsJson026.getObjVal? "physical_volume" = .ok (.str geometryRow026_physicalVolumeText) := by rfl

theorem geometryRow026_physicalVolume_numerator_no_slash :
    geometryRow026_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow026_physicalVolumeNumeratorChars = some (968720252589769422775974500218167343 : Int) := by decide +kernel

theorem geometryRow026_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow026_physicalVolumeDenominatorChars = some (66186055800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow026_physicalVolume_denominator_nonzero : (66186055800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_physicalVolume_parse :
    parseRational geometryRow026_physicalVolumeText = .ok geometryRowsTyped026.physicalVolume :=
  original_rational_fraction_of_chars geometryRow026_physicalVolumeNumeratorChars geometryRow026_physicalVolumeDenominatorChars
    (968720252589769422775974500218167343 : Int) (66186055800000000000000000000000000000000000000000000000000 : Int)
    geometryRow026_physicalVolume_numerator_no_slash geometryRow026_physicalVolume_numerator_parse
    geometryRow026_physicalVolume_denominator_parse geometryRow026_physicalVolume_denominator_nonzero

theorem geometryRow026_physicalVolume_read :
    rationalField geometryRowsJson026 "physical_volume" = .ok geometryRowsTyped026.physicalVolume :=
  original_rationalField_of_string geometryRowsJson026 "physical_volume" geometryRow026_physicalVolumeText
    geometryRowsTyped026.physicalVolume geometryRow026_physicalVolume_field geometryRow026_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_physicalVolume_complete"
  err.flush

noncomputable def geometryRow026_meanGapNumeratorChars : List Char := ['1', '0', '8', '2', '4', '1', '6', '9']
noncomputable def geometryRow026_meanGapDenominatorChars : List Char := ['1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow026_meanGapText : String := String.ofList (geometryRow026_meanGapNumeratorChars ++ '/' :: geometryRow026_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_meanGap_before_field"
  err.flush

theorem geometryRow026_meanGap_field :
    geometryRowsJson026.getObjVal? "mean_gap" = .ok (.str geometryRow026_meanGapText) := by rfl

theorem geometryRow026_meanGap_numerator_no_slash :
    geometryRow026_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_meanGap_numerator_parse :
    SourceJson.intChars geometryRow026_meanGapNumeratorChars = some (10824169 : Int) := by decide +kernel

theorem geometryRow026_meanGap_denominator_parse :
    SourceJson.intChars geometryRow026_meanGapDenominatorChars = some (19584000000 : Int) := by decide +kernel

theorem geometryRow026_meanGap_denominator_nonzero : (19584000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_meanGap_parse :
    parseRational geometryRow026_meanGapText = .ok geometryRowsTyped026.meanGap :=
  original_rational_fraction_of_chars geometryRow026_meanGapNumeratorChars geometryRow026_meanGapDenominatorChars
    (10824169 : Int) (19584000000 : Int)
    geometryRow026_meanGap_numerator_no_slash geometryRow026_meanGap_numerator_parse
    geometryRow026_meanGap_denominator_parse geometryRow026_meanGap_denominator_nonzero

theorem geometryRow026_meanGap_read :
    rationalField geometryRowsJson026 "mean_gap" = .ok geometryRowsTyped026.meanGap :=
  original_rationalField_of_string geometryRowsJson026 "mean_gap" geometryRow026_meanGapText
    geometryRowsTyped026.meanGap geometryRow026_meanGap_field geometryRow026_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_meanGap_complete"
  err.flush

noncomputable def geometryRow026_jensenBoundNumeratorChars : List Char := ['5', '8', '7', '6', '8', '1', '0', '5', '6', '5', '7', '9', '9', '1', '3', '1', '1', '2', '1', '2', '4', '3', '8', '1', '7', '7', '8', '1', '6', '2', '9', '3', '7', '1', '8', '5', '1', '0', '0', '8', '8', '8', '6', '3', '7', '5', '3', '6', '9', '8', '3', '0', '7', '6', '4', '6', '8', '2', '8', '2', '8', '1', '3', '0', '6', '8', '5', '0', '6', '8', '6', '8', '0', '2', '0', '0', '1', '4', '0', '1', '1', '0', '8', '8', '4', '3', '6', '1', '5', '4', '3', '7', '7', '1', '4', '6', '6', '2', '6', '4', '6', '3', '9', '2', '1', '4', '5', '1', '7', '0', '8', '3', '6', '8', '8', '5', '9', '9', '9', '0', '2', '7', '7', '0', '3', '5', '2', '3', '6', '6', '5', '3', '5', '7', '4', '8', '6', '1', '0', '7', '0', '2', '6', '0', '9', '4', '9', '6', '3', '8', '0', '5', '4', '5', '1', '7', '4', '0', '7', '6', '5', '7', '4', '2', '9', '5', '6', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow026_jensenBoundDenominatorChars : List Char := ['1', '1', '7', '8', '8', '9', '4', '0', '7', '1', '9', '2', '7', '9', '3', '5', '3', '5', '9', '6', '5', '9', '9', '7', '7', '4', '7', '2', '8', '9', '0', '0', '2', '5', '3', '1', '2', '1', '1', '3', '8', '6', '3', '7', '0', '8', '9', '6', '4', '0', '1', '6', '7', '9', '3', '7', '4', '4', '3', '4', '5', '3', '2', '2', '7', '9', '5', '6', '5', '2', '9', '2', '8', '2', '4', '8', '3', '4', '8', '9', '7', '3', '7', '1', '1', '6', '5', '1', '0', '6', '9', '0', '6', '9', '0', '4', '2', '6', '3', '8', '3', '8', '7', '4', '1', '5', '0', '0', '5', '9', '1', '3', '7', '8', '4', '4', '4', '7', '2', '6', '4', '8', '3', '3', '1', '8', '4', '3', '7', '0', '8', '7', '8', '0', '1', '9', '0', '7', '3', '6', '9', '6', '0', '9', '6', '0', '8', '4', '9', '7', '8', '5', '9', '2', '2', '3', '1', '0', '2', '7', '7', '9', '3', '5', '1', '1', '0', '9', '0', '4', '9', '8', '3', '2', '5', '2', '0', '4', '7', '3', '6', '5', '0', '1', '5', '2', '7', '0', '0', '2', '8', '5', '0', '7', '8', '0', '8', '5', '6', '8', '7', '7', '9', '3', '3']
noncomputable def geometryRow026_jensenBoundText : String := String.ofList (geometryRow026_jensenBoundNumeratorChars ++ '/' :: geometryRow026_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_jensenBound_before_field"
  err.flush

theorem geometryRow026_jensenBound_field :
    geometryRowsJson026.getObjVal? "jensen_bound" = .ok (.str geometryRow026_jensenBoundText) := by rfl

theorem geometryRow026_jensenBound_numerator_no_slash :
    geometryRow026_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow026_jensenBoundNumeratorChars = some (58768105657991311212438177816293718510088863753698307646828281306850686802001401108843615437714662646392145170836885999027703523665357486107026094963805451740765742956544000000000000000000000 : Int) := by decide +kernel

theorem geometryRow026_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow026_jensenBoundDenominatorChars = some (1178894071927935359659977472890025312113863708964016793744345322795652928248348973711651069069042638387415005913784447264833184370878019073696096084978592231027793511090498325204736501527002850780856877933 : Int) := by decide +kernel

theorem geometryRow026_jensenBound_denominator_nonzero : (1178894071927935359659977472890025312113863708964016793744345322795652928248348973711651069069042638387415005913784447264833184370878019073696096084978592231027793511090498325204736501527002850780856877933 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_jensenBound_parse :
    parseRational geometryRow026_jensenBoundText = .ok geometryRowsTyped026.jensenBound :=
  original_rational_fraction_of_chars geometryRow026_jensenBoundNumeratorChars geometryRow026_jensenBoundDenominatorChars
    (58768105657991311212438177816293718510088863753698307646828281306850686802001401108843615437714662646392145170836885999027703523665357486107026094963805451740765742956544000000000000000000000 : Int) (1178894071927935359659977472890025312113863708964016793744345322795652928248348973711651069069042638387415005913784447264833184370878019073696096084978592231027793511090498325204736501527002850780856877933 : Int)
    geometryRow026_jensenBound_numerator_no_slash geometryRow026_jensenBound_numerator_parse
    geometryRow026_jensenBound_denominator_parse geometryRow026_jensenBound_denominator_nonzero

theorem geometryRow026_jensenBound_read :
    rationalField geometryRowsJson026 "jensen_bound" = .ok geometryRowsTyped026.jensenBound :=
  original_rationalField_of_string geometryRowsJson026 "jensen_bound" geometryRow026_jensenBoundText
    geometryRowsTyped026.jensenBound geometryRow026_jensenBound_field geometryRow026_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_factorMaxima_before"
  err.flush

theorem geometryRow026_factorMaxima_read :
    rationalArrayField geometryRowsJson026 "factor_maxima" = .ok geometryRowsTyped026.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_gapWeightedMeans_before"
  err.flush

theorem geometryRow026_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson026 "gap_weighted_means" = .ok geometryRowsTyped026.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow026_floorChars : List Char := ['3', '9', '4', '9', '5', '3', '9', '7', '7', '3', '4', '1', '8', '6', '0', '3']
noncomputable def geometryRow026_floorText : String := String.ofList geometryRow026_floorChars

theorem geometryRow026_floor_text_read :
    geometryRowsJson026.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow026_floorText := by rfl

theorem geometryRow026_floor_chars_parse :
    SourceJson.intChars geometryRow026_floorChars = some (3949539773418603 : Int) := by decide +kernel

theorem geometryRow026_floor_parse :
    parseInteger geometryRow026_floorText = .ok geometryRowsTyped026.jensenFloorQ96 := by
  simp only [geometryRow026_floorText, parseInteger, String.toList_ofList, geometryRow026_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_026 :
    decodeGeometryRow geometryRowsJson026 = .ok geometryRowsTyped026 :=
  original_geometryRow_of_fields geometryRowsJson026 geometryRowsTyped026 geometryRow026_floorText
    geometryRow026_simplexId_read geometryRow026_vertexIds_read
    geometryRow026_physicalVolume_read geometryRow026_meanGap_read
    geometryRow026_factorMaxima_read geometryRow026_gapWeightedMeans_read
    geometryRow026_jensenBound_read geometryRow026_floor_text_read geometryRow026_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_026_original_decoder_complete"
  err.flush

theorem geometryRow026_shape :
    geometryRowsTyped026.simplexId = 26 ∧
    geometryRowsTyped026.vertexIds.size = 9 ∧ geometryRowsTyped026.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped026.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped026.factorMaxima.size = 10 ∧ geometryRowsTyped026.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson027 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped027 : GeometryRow :=
  { simplexId := 27,
    vertexIds := #[27, 25, 23, 21, 19, 17, 16, 4, 0],
    physicalVolume := ((328018259033845342897557686173 : ℚ) / (54073575000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2409379 : ℚ) / (25600000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((17290930045681 : ℚ) / (199382400000000 : ℚ)), ((2174139541187 : ℚ) / (24922800000000 : ℚ)), ((493306936691 : ℚ) / (3987648000000 : ℚ)), ((4733502211567 : ℚ) / (49845600000000 : ℚ)), ((4582162121813 : ℚ) / (49845600000000 : ℚ)), ((140283058439 : ℚ) / (1993824000000 : ℚ)), ((3839875001869 : ℚ) / (99691200000000 : ℚ)), ((1028435615707 : ℚ) / (33230400000000 : ℚ)), ((333572959049 : ℚ) / (11076800000000 : ℚ)), ((247337888363 : ℚ) / (8307600000000 : ℚ))],
    jensenBound := ((18794758515506153029348297914054328533448445118857054132314802744308641996385497907200000000000000000000 : ℚ) / (1671337849044939439244806718534723265775919975347231264709821338309601001054314892679826856297588088865741332304956181043 : ℚ)),
    jensenFloorQ96 := (890947442453 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_simplexId_before"
  err.flush

theorem geometryRow027_simplexId_read :
    geometryRowsJson027.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped027.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_vertexIds_before"
  err.flush

theorem geometryRow027_vertexIds_read :
    geometryRowsJson027.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped027.vertexIds := by decide +kernel

noncomputable def geometryRow027_physicalVolumeNumeratorChars : List Char := ['3', '2', '8', '0', '1', '8', '2', '5', '9', '0', '3', '3', '8', '4', '5', '3', '4', '2', '8', '9', '7', '5', '5', '7', '6', '8', '6', '1', '7', '3']
noncomputable def geometryRow027_physicalVolumeDenominatorChars : List Char := ['5', '4', '0', '7', '3', '5', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_physicalVolumeText : String := String.ofList (geometryRow027_physicalVolumeNumeratorChars ++ '/' :: geometryRow027_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_physicalVolume_before_field"
  err.flush

theorem geometryRow027_physicalVolume_field :
    geometryRowsJson027.getObjVal? "physical_volume" = .ok (.str geometryRow027_physicalVolumeText) := by rfl

theorem geometryRow027_physicalVolume_numerator_no_slash :
    geometryRow027_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow027_physicalVolumeNumeratorChars = some (328018259033845342897557686173 : Int) := by decide +kernel

theorem geometryRow027_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow027_physicalVolumeDenominatorChars = some (54073575000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow027_physicalVolume_denominator_nonzero : (54073575000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_physicalVolume_parse :
    parseRational geometryRow027_physicalVolumeText = .ok geometryRowsTyped027.physicalVolume :=
  original_rational_fraction_of_chars geometryRow027_physicalVolumeNumeratorChars geometryRow027_physicalVolumeDenominatorChars
    (328018259033845342897557686173 : Int) (54073575000000000000000000000000000000000000000000000000 : Int)
    geometryRow027_physicalVolume_numerator_no_slash geometryRow027_physicalVolume_numerator_parse
    geometryRow027_physicalVolume_denominator_parse geometryRow027_physicalVolume_denominator_nonzero

theorem geometryRow027_physicalVolume_read :
    rationalField geometryRowsJson027 "physical_volume" = .ok geometryRowsTyped027.physicalVolume :=
  original_rationalField_of_string geometryRowsJson027 "physical_volume" geometryRow027_physicalVolumeText
    geometryRowsTyped027.physicalVolume geometryRow027_physicalVolume_field geometryRow027_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_physicalVolume_complete"
  err.flush

noncomputable def geometryRow027_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow027_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_meanGapText : String := String.ofList (geometryRow027_meanGapNumeratorChars ++ '/' :: geometryRow027_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_meanGap_before_field"
  err.flush

theorem geometryRow027_meanGap_field :
    geometryRowsJson027.getObjVal? "mean_gap" = .ok (.str geometryRow027_meanGapText) := by rfl

theorem geometryRow027_meanGap_numerator_no_slash :
    geometryRow027_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_meanGap_numerator_parse :
    SourceJson.intChars geometryRow027_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow027_meanGap_denominator_parse :
    SourceJson.intChars geometryRow027_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow027_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_meanGap_parse :
    parseRational geometryRow027_meanGapText = .ok geometryRowsTyped027.meanGap :=
  original_rational_fraction_of_chars geometryRow027_meanGapNumeratorChars geometryRow027_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow027_meanGap_numerator_no_slash geometryRow027_meanGap_numerator_parse
    geometryRow027_meanGap_denominator_parse geometryRow027_meanGap_denominator_nonzero

theorem geometryRow027_meanGap_read :
    rationalField geometryRowsJson027 "mean_gap" = .ok geometryRowsTyped027.meanGap :=
  original_rationalField_of_string geometryRowsJson027 "mean_gap" geometryRow027_meanGapText
    geometryRowsTyped027.meanGap geometryRow027_meanGap_field geometryRow027_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_meanGap_complete"
  err.flush

noncomputable def geometryRow027_jensenBoundNumeratorChars : List Char := ['1', '8', '7', '9', '4', '7', '5', '8', '5', '1', '5', '5', '0', '6', '1', '5', '3', '0', '2', '9', '3', '4', '8', '2', '9', '7', '9', '1', '4', '0', '5', '4', '3', '2', '8', '5', '3', '3', '4', '4', '8', '4', '4', '5', '1', '1', '8', '8', '5', '7', '0', '5', '4', '1', '3', '2', '3', '1', '4', '8', '0', '2', '7', '4', '4', '3', '0', '8', '6', '4', '1', '9', '9', '6', '3', '8', '5', '4', '9', '7', '9', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_jensenBoundDenominatorChars : List Char := ['1', '6', '7', '1', '3', '3', '7', '8', '4', '9', '0', '4', '4', '9', '3', '9', '4', '3', '9', '2', '4', '4', '8', '0', '6', '7', '1', '8', '5', '3', '4', '7', '2', '3', '2', '6', '5', '7', '7', '5', '9', '1', '9', '9', '7', '5', '3', '4', '7', '2', '3', '1', '2', '6', '4', '7', '0', '9', '8', '2', '1', '3', '3', '8', '3', '0', '9', '6', '0', '1', '0', '0', '1', '0', '5', '4', '3', '1', '4', '8', '9', '2', '6', '7', '9', '8', '2', '6', '8', '5', '6', '2', '9', '7', '5', '8', '8', '0', '8', '8', '8', '6', '5', '7', '4', '1', '3', '3', '2', '3', '0', '4', '9', '5', '6', '1', '8', '1', '0', '4', '3']
noncomputable def geometryRow027_jensenBoundText : String := String.ofList (geometryRow027_jensenBoundNumeratorChars ++ '/' :: geometryRow027_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_jensenBound_before_field"
  err.flush

theorem geometryRow027_jensenBound_field :
    geometryRowsJson027.getObjVal? "jensen_bound" = .ok (.str geometryRow027_jensenBoundText) := by rfl

theorem geometryRow027_jensenBound_numerator_no_slash :
    geometryRow027_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow027_jensenBoundNumeratorChars = some (18794758515506153029348297914054328533448445118857054132314802744308641996385497907200000000000000000000 : Int) := by decide +kernel

theorem geometryRow027_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow027_jensenBoundDenominatorChars = some (1671337849044939439244806718534723265775919975347231264709821338309601001054314892679826856297588088865741332304956181043 : Int) := by decide +kernel

theorem geometryRow027_jensenBound_denominator_nonzero : (1671337849044939439244806718534723265775919975347231264709821338309601001054314892679826856297588088865741332304956181043 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_jensenBound_parse :
    parseRational geometryRow027_jensenBoundText = .ok geometryRowsTyped027.jensenBound :=
  original_rational_fraction_of_chars geometryRow027_jensenBoundNumeratorChars geometryRow027_jensenBoundDenominatorChars
    (18794758515506153029348297914054328533448445118857054132314802744308641996385497907200000000000000000000 : Int) (1671337849044939439244806718534723265775919975347231264709821338309601001054314892679826856297588088865741332304956181043 : Int)
    geometryRow027_jensenBound_numerator_no_slash geometryRow027_jensenBound_numerator_parse
    geometryRow027_jensenBound_denominator_parse geometryRow027_jensenBound_denominator_nonzero

theorem geometryRow027_jensenBound_read :
    rationalField geometryRowsJson027 "jensen_bound" = .ok geometryRowsTyped027.jensenBound :=
  original_rationalField_of_string geometryRowsJson027 "jensen_bound" geometryRow027_jensenBoundText
    geometryRowsTyped027.jensenBound geometryRow027_jensenBound_field geometryRow027_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_factorMaxima_before"
  err.flush

theorem geometryRow027_factorMaxima_read :
    rationalArrayField geometryRowsJson027 "factor_maxima" = .ok geometryRowsTyped027.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_gapWeightedMeans_before"
  err.flush

theorem geometryRow027_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson027 "gap_weighted_means" = .ok geometryRowsTyped027.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow027_floorChars : List Char := ['8', '9', '0', '9', '4', '7', '4', '4', '2', '4', '5', '3']
noncomputable def geometryRow027_floorText : String := String.ofList geometryRow027_floorChars

theorem geometryRow027_floor_text_read :
    geometryRowsJson027.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow027_floorText := by rfl

theorem geometryRow027_floor_chars_parse :
    SourceJson.intChars geometryRow027_floorChars = some (890947442453 : Int) := by decide +kernel

theorem geometryRow027_floor_parse :
    parseInteger geometryRow027_floorText = .ok geometryRowsTyped027.jensenFloorQ96 := by
  simp only [geometryRow027_floorText, parseInteger, String.toList_ofList, geometryRow027_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_027 :
    decodeGeometryRow geometryRowsJson027 = .ok geometryRowsTyped027 :=
  original_geometryRow_of_fields geometryRowsJson027 geometryRowsTyped027 geometryRow027_floorText
    geometryRow027_simplexId_read geometryRow027_vertexIds_read
    geometryRow027_physicalVolume_read geometryRow027_meanGap_read
    geometryRow027_factorMaxima_read geometryRow027_gapWeightedMeans_read
    geometryRow027_jensenBound_read geometryRow027_floor_text_read geometryRow027_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_027_original_decoder_complete"
  err.flush

theorem geometryRow027_shape :
    geometryRowsTyped027.simplexId = 27 ∧
    geometryRowsTyped027.vertexIds.size = 9 ∧ geometryRowsTyped027.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped027.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped027.factorMaxima.size = 10 ∧ geometryRowsTyped027.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson028 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped028 : GeometryRow :=
  { simplexId := 28,
    vertexIds := #[27, 25, 23, 21, 19, 17, 16, 14, 4],
    physicalVolume := ((1458598058224984567994545831081 : ℚ) / (430898800781250000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((51871037 : ℚ) / (97920000000 : ℚ)),
    factorMaxima := #[((2409379 : ℚ) / (25600000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2390621 : ℚ) / (32000000 : ℚ)), ((515597 : ℚ) / (12000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((2148890722497846660139 : ℚ) / (25116703058332800000000 : ℚ)), ((270860775824084008691 : ℚ) / (3139587882291600000000 : ℚ)), ((1570784980282545721601 : ℚ) / (12558351529166400000000 : ℚ)), ((609470168737117090261 : ℚ) / (6279175764583200000000 : ℚ)), ((586990262775737610167 : ℚ) / (6279175764583200000000 : ℚ)), ((86126063669605360789 : ℚ) / (1255835152916640000000 : ℚ)), ((27277018990930568207 : ℚ) / (738726560539200000000 : ℚ)), ((128781134574056858417 : ℚ) / (4186117176388800000000 : ℚ)), ((125289587215027362097 : ℚ) / (4186117176388800000000 : ℚ)), ((30822103633849606939 : ℚ) / (1046529294097200000000 : ℚ))],
    jensenBound := ((680674551604057566908755133963140723978177250380682496798644510891021145232711815425134702448712170899227737885418756422240029157160682404584516360274124964697735168000000000000000000000 : ℚ) / (54591308701226937556462129805148229054065467034514564295053595378786454517234469592844445635962079437792891340727031007849493557884204114547477258126773085439882391386174653726310178170732940873347613677 : ℚ)),
    jensenFloorQ96 := (987860435604 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_simplexId_before"
  err.flush

theorem geometryRow028_simplexId_read :
    geometryRowsJson028.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped028.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_vertexIds_before"
  err.flush

theorem geometryRow028_vertexIds_read :
    geometryRowsJson028.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped028.vertexIds := by decide +kernel

noncomputable def geometryRow028_physicalVolumeNumeratorChars : List Char := ['1', '4', '5', '8', '5', '9', '8', '0', '5', '8', '2', '2', '4', '9', '8', '4', '5', '6', '7', '9', '9', '4', '5', '4', '5', '8', '3', '1', '0', '8', '1']
noncomputable def geometryRow028_physicalVolumeDenominatorChars : List Char := ['4', '3', '0', '8', '9', '8', '8', '0', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_physicalVolumeText : String := String.ofList (geometryRow028_physicalVolumeNumeratorChars ++ '/' :: geometryRow028_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_physicalVolume_before_field"
  err.flush

theorem geometryRow028_physicalVolume_field :
    geometryRowsJson028.getObjVal? "physical_volume" = .ok (.str geometryRow028_physicalVolumeText) := by rfl

theorem geometryRow028_physicalVolume_numerator_no_slash :
    geometryRow028_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow028_physicalVolumeNumeratorChars = some (1458598058224984567994545831081 : Int) := by decide +kernel

theorem geometryRow028_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow028_physicalVolumeDenominatorChars = some (430898800781250000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow028_physicalVolume_denominator_nonzero : (430898800781250000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_physicalVolume_parse :
    parseRational geometryRow028_physicalVolumeText = .ok geometryRowsTyped028.physicalVolume :=
  original_rational_fraction_of_chars geometryRow028_physicalVolumeNumeratorChars geometryRow028_physicalVolumeDenominatorChars
    (1458598058224984567994545831081 : Int) (430898800781250000000000000000000000000000000000000000000 : Int)
    geometryRow028_physicalVolume_numerator_no_slash geometryRow028_physicalVolume_numerator_parse
    geometryRow028_physicalVolume_denominator_parse geometryRow028_physicalVolume_denominator_nonzero

theorem geometryRow028_physicalVolume_read :
    rationalField geometryRowsJson028 "physical_volume" = .ok geometryRowsTyped028.physicalVolume :=
  original_rationalField_of_string geometryRowsJson028 "physical_volume" geometryRow028_physicalVolumeText
    geometryRowsTyped028.physicalVolume geometryRow028_physicalVolume_field geometryRow028_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_physicalVolume_complete"
  err.flush

noncomputable def geometryRow028_meanGapNumeratorChars : List Char := ['5', '1', '8', '7', '1', '0', '3', '7']
noncomputable def geometryRow028_meanGapDenominatorChars : List Char := ['9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_meanGapText : String := String.ofList (geometryRow028_meanGapNumeratorChars ++ '/' :: geometryRow028_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_meanGap_before_field"
  err.flush

theorem geometryRow028_meanGap_field :
    geometryRowsJson028.getObjVal? "mean_gap" = .ok (.str geometryRow028_meanGapText) := by rfl

theorem geometryRow028_meanGap_numerator_no_slash :
    geometryRow028_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_meanGap_numerator_parse :
    SourceJson.intChars geometryRow028_meanGapNumeratorChars = some (51871037 : Int) := by decide +kernel

theorem geometryRow028_meanGap_denominator_parse :
    SourceJson.intChars geometryRow028_meanGapDenominatorChars = some (97920000000 : Int) := by decide +kernel

theorem geometryRow028_meanGap_denominator_nonzero : (97920000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_meanGap_parse :
    parseRational geometryRow028_meanGapText = .ok geometryRowsTyped028.meanGap :=
  original_rational_fraction_of_chars geometryRow028_meanGapNumeratorChars geometryRow028_meanGapDenominatorChars
    (51871037 : Int) (97920000000 : Int)
    geometryRow028_meanGap_numerator_no_slash geometryRow028_meanGap_numerator_parse
    geometryRow028_meanGap_denominator_parse geometryRow028_meanGap_denominator_nonzero

theorem geometryRow028_meanGap_read :
    rationalField geometryRowsJson028 "mean_gap" = .ok geometryRowsTyped028.meanGap :=
  original_rationalField_of_string geometryRowsJson028 "mean_gap" geometryRow028_meanGapText
    geometryRowsTyped028.meanGap geometryRow028_meanGap_field geometryRow028_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_meanGap_complete"
  err.flush

noncomputable def geometryRow028_jensenBoundNumeratorChars : List Char := ['6', '8', '0', '6', '7', '4', '5', '5', '1', '6', '0', '4', '0', '5', '7', '5', '6', '6', '9', '0', '8', '7', '5', '5', '1', '3', '3', '9', '6', '3', '1', '4', '0', '7', '2', '3', '9', '7', '8', '1', '7', '7', '2', '5', '0', '3', '8', '0', '6', '8', '2', '4', '9', '6', '7', '9', '8', '6', '4', '4', '5', '1', '0', '8', '9', '1', '0', '2', '1', '1', '4', '5', '2', '3', '2', '7', '1', '1', '8', '1', '5', '4', '2', '5', '1', '3', '4', '7', '0', '2', '4', '4', '8', '7', '1', '2', '1', '7', '0', '8', '9', '9', '2', '2', '7', '7', '3', '7', '8', '8', '5', '4', '1', '8', '7', '5', '6', '4', '2', '2', '2', '4', '0', '0', '2', '9', '1', '5', '7', '1', '6', '0', '6', '8', '2', '4', '0', '4', '5', '8', '4', '5', '1', '6', '3', '6', '0', '2', '7', '4', '1', '2', '4', '9', '6', '4', '6', '9', '7', '7', '3', '5', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_jensenBoundDenominatorChars : List Char := ['5', '4', '5', '9', '1', '3', '0', '8', '7', '0', '1', '2', '2', '6', '9', '3', '7', '5', '5', '6', '4', '6', '2', '1', '2', '9', '8', '0', '5', '1', '4', '8', '2', '2', '9', '0', '5', '4', '0', '6', '5', '4', '6', '7', '0', '3', '4', '5', '1', '4', '5', '6', '4', '2', '9', '5', '0', '5', '3', '5', '9', '5', '3', '7', '8', '7', '8', '6', '4', '5', '4', '5', '1', '7', '2', '3', '4', '4', '6', '9', '5', '9', '2', '8', '4', '4', '4', '4', '5', '6', '3', '5', '9', '6', '2', '0', '7', '9', '4', '3', '7', '7', '9', '2', '8', '9', '1', '3', '4', '0', '7', '2', '7', '0', '3', '1', '0', '0', '7', '8', '4', '9', '4', '9', '3', '5', '5', '7', '8', '8', '4', '2', '0', '4', '1', '1', '4', '5', '4', '7', '4', '7', '7', '2', '5', '8', '1', '2', '6', '7', '7', '3', '0', '8', '5', '4', '3', '9', '8', '8', '2', '3', '9', '1', '3', '8', '6', '1', '7', '4', '6', '5', '3', '7', '2', '6', '3', '1', '0', '1', '7', '8', '1', '7', '0', '7', '3', '2', '9', '4', '0', '8', '7', '3', '3', '4', '7', '6', '1', '3', '6', '7', '7']
noncomputable def geometryRow028_jensenBoundText : String := String.ofList (geometryRow028_jensenBoundNumeratorChars ++ '/' :: geometryRow028_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_jensenBound_before_field"
  err.flush

theorem geometryRow028_jensenBound_field :
    geometryRowsJson028.getObjVal? "jensen_bound" = .ok (.str geometryRow028_jensenBoundText) := by rfl

theorem geometryRow028_jensenBound_numerator_no_slash :
    geometryRow028_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow028_jensenBoundNumeratorChars = some (680674551604057566908755133963140723978177250380682496798644510891021145232711815425134702448712170899227737885418756422240029157160682404584516360274124964697735168000000000000000000000 : Int) := by decide +kernel

theorem geometryRow028_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow028_jensenBoundDenominatorChars = some (54591308701226937556462129805148229054065467034514564295053595378786454517234469592844445635962079437792891340727031007849493557884204114547477258126773085439882391386174653726310178170732940873347613677 : Int) := by decide +kernel

theorem geometryRow028_jensenBound_denominator_nonzero : (54591308701226937556462129805148229054065467034514564295053595378786454517234469592844445635962079437792891340727031007849493557884204114547477258126773085439882391386174653726310178170732940873347613677 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_jensenBound_parse :
    parseRational geometryRow028_jensenBoundText = .ok geometryRowsTyped028.jensenBound :=
  original_rational_fraction_of_chars geometryRow028_jensenBoundNumeratorChars geometryRow028_jensenBoundDenominatorChars
    (680674551604057566908755133963140723978177250380682496798644510891021145232711815425134702448712170899227737885418756422240029157160682404584516360274124964697735168000000000000000000000 : Int) (54591308701226937556462129805148229054065467034514564295053595378786454517234469592844445635962079437792891340727031007849493557884204114547477258126773085439882391386174653726310178170732940873347613677 : Int)
    geometryRow028_jensenBound_numerator_no_slash geometryRow028_jensenBound_numerator_parse
    geometryRow028_jensenBound_denominator_parse geometryRow028_jensenBound_denominator_nonzero

theorem geometryRow028_jensenBound_read :
    rationalField geometryRowsJson028 "jensen_bound" = .ok geometryRowsTyped028.jensenBound :=
  original_rationalField_of_string geometryRowsJson028 "jensen_bound" geometryRow028_jensenBoundText
    geometryRowsTyped028.jensenBound geometryRow028_jensenBound_field geometryRow028_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_factorMaxima_before"
  err.flush

theorem geometryRow028_factorMaxima_read :
    rationalArrayField geometryRowsJson028 "factor_maxima" = .ok geometryRowsTyped028.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_gapWeightedMeans_before"
  err.flush

theorem geometryRow028_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson028 "gap_weighted_means" = .ok geometryRowsTyped028.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow028_floorChars : List Char := ['9', '8', '7', '8', '6', '0', '4', '3', '5', '6', '0', '4']
noncomputable def geometryRow028_floorText : String := String.ofList geometryRow028_floorChars

theorem geometryRow028_floor_text_read :
    geometryRowsJson028.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow028_floorText := by rfl

theorem geometryRow028_floor_chars_parse :
    SourceJson.intChars geometryRow028_floorChars = some (987860435604 : Int) := by decide +kernel

theorem geometryRow028_floor_parse :
    parseInteger geometryRow028_floorText = .ok geometryRowsTyped028.jensenFloorQ96 := by
  simp only [geometryRow028_floorText, parseInteger, String.toList_ofList, geometryRow028_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_028 :
    decodeGeometryRow geometryRowsJson028 = .ok geometryRowsTyped028 :=
  original_geometryRow_of_fields geometryRowsJson028 geometryRowsTyped028 geometryRow028_floorText
    geometryRow028_simplexId_read geometryRow028_vertexIds_read
    geometryRow028_physicalVolume_read geometryRow028_meanGap_read
    geometryRow028_factorMaxima_read geometryRow028_gapWeightedMeans_read
    geometryRow028_jensenBound_read geometryRow028_floor_text_read geometryRow028_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_028_original_decoder_complete"
  err.flush

theorem geometryRow028_shape :
    geometryRowsTyped028.simplexId = 28 ∧
    geometryRowsTyped028.vertexIds.size = 9 ∧ geometryRowsTyped028.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped028.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped028.factorMaxima.size = 10 ∧ geometryRowsTyped028.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson029 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped029 : GeometryRow :=
  { simplexId := 29,
    vertexIds := #[27, 25, 23, 21, 19, 17, 15, 5, 4],
    physicalVolume := ((1225759630992054725915674776706964477 : ℚ) / (143403120900000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((22108269 : ℚ) / (28288000000 : ℚ)),
    factorMaxima := #[((12984403 : ℚ) / (136000000 : ℚ)), ((3328101 : ℚ) / (34000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2546871 : ℚ) / (34000000 : ℚ)), ((515593 : ℚ) / (12000000 : ℚ)), ((2328113 : ℚ) / (68000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ))],
    gapWeightedMeans := #[((4044497497959382994629 : ℚ) / (46388949571785600000000 : ℚ)), ((39308570304181045711 : ℚ) / (446047592036400000000 : ℚ)), ((63947354895672077899 : ℚ) / (515432773019840000000 : ℚ)), ((1111910937824688921343 : ℚ) / (11597237392946400000000 : ℚ)), ((3190461350028720440791 : ℚ) / (34791712178839200000000 : ℚ)), ((160384496034591196499 : ℚ) / (2319447478589280000000 : ℚ)), ((2555426466617979172763 : ℚ) / (69583424357678400000000 : ℚ)), ((2194007527628007339487 : ℚ) / (69583424357678400000000 : ℚ)), ((162198601756090904419 : ℚ) / (5352571104436800000000 : ℚ)), ((13412486486170830917 : ℚ) / (446047592036400000000 : ℚ))],
    jensenBound := ((280287940456286478683605086158109772491900663103910630045391531677110658532644922009583196869206692580671682291345371988646388496733717684951904161581855666797312401735680000000000000000000000 : ℚ) / (6413948945556045043137684494115367417588138525763083602245170401788822739714580388011399846884392185643149708251880461562839614699054248692025329741933250417101573637662737431768686823622762625070279540051 : ℚ)),
    jensenFloorQ96 := (3462250586301469 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_simplexId_before"
  err.flush

theorem geometryRow029_simplexId_read :
    geometryRowsJson029.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped029.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_vertexIds_before"
  err.flush

theorem geometryRow029_vertexIds_read :
    geometryRowsJson029.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped029.vertexIds := by decide +kernel

noncomputable def geometryRow029_physicalVolumeNumeratorChars : List Char := ['1', '2', '2', '5', '7', '5', '9', '6', '3', '0', '9', '9', '2', '0', '5', '4', '7', '2', '5', '9', '1', '5', '6', '7', '4', '7', '7', '6', '7', '0', '6', '9', '6', '4', '4', '7', '7']
noncomputable def geometryRow029_physicalVolumeDenominatorChars : List Char := ['1', '4', '3', '4', '0', '3', '1', '2', '0', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_physicalVolumeText : String := String.ofList (geometryRow029_physicalVolumeNumeratorChars ++ '/' :: geometryRow029_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_physicalVolume_before_field"
  err.flush

theorem geometryRow029_physicalVolume_field :
    geometryRowsJson029.getObjVal? "physical_volume" = .ok (.str geometryRow029_physicalVolumeText) := by rfl

theorem geometryRow029_physicalVolume_numerator_no_slash :
    geometryRow029_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow029_physicalVolumeNumeratorChars = some (1225759630992054725915674776706964477 : Int) := by decide +kernel

theorem geometryRow029_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow029_physicalVolumeDenominatorChars = some (143403120900000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow029_physicalVolume_denominator_nonzero : (143403120900000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_physicalVolume_parse :
    parseRational geometryRow029_physicalVolumeText = .ok geometryRowsTyped029.physicalVolume :=
  original_rational_fraction_of_chars geometryRow029_physicalVolumeNumeratorChars geometryRow029_physicalVolumeDenominatorChars
    (1225759630992054725915674776706964477 : Int) (143403120900000000000000000000000000000000000000000000000000 : Int)
    geometryRow029_physicalVolume_numerator_no_slash geometryRow029_physicalVolume_numerator_parse
    geometryRow029_physicalVolume_denominator_parse geometryRow029_physicalVolume_denominator_nonzero

theorem geometryRow029_physicalVolume_read :
    rationalField geometryRowsJson029 "physical_volume" = .ok geometryRowsTyped029.physicalVolume :=
  original_rationalField_of_string geometryRowsJson029 "physical_volume" geometryRow029_physicalVolumeText
    geometryRowsTyped029.physicalVolume geometryRow029_physicalVolume_field geometryRow029_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_physicalVolume_complete"
  err.flush

noncomputable def geometryRow029_meanGapNumeratorChars : List Char := ['2', '2', '1', '0', '8', '2', '6', '9']
noncomputable def geometryRow029_meanGapDenominatorChars : List Char := ['2', '8', '2', '8', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_meanGapText : String := String.ofList (geometryRow029_meanGapNumeratorChars ++ '/' :: geometryRow029_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_meanGap_before_field"
  err.flush

theorem geometryRow029_meanGap_field :
    geometryRowsJson029.getObjVal? "mean_gap" = .ok (.str geometryRow029_meanGapText) := by rfl

theorem geometryRow029_meanGap_numerator_no_slash :
    geometryRow029_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_meanGap_numerator_parse :
    SourceJson.intChars geometryRow029_meanGapNumeratorChars = some (22108269 : Int) := by decide +kernel

theorem geometryRow029_meanGap_denominator_parse :
    SourceJson.intChars geometryRow029_meanGapDenominatorChars = some (28288000000 : Int) := by decide +kernel

theorem geometryRow029_meanGap_denominator_nonzero : (28288000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_meanGap_parse :
    parseRational geometryRow029_meanGapText = .ok geometryRowsTyped029.meanGap :=
  original_rational_fraction_of_chars geometryRow029_meanGapNumeratorChars geometryRow029_meanGapDenominatorChars
    (22108269 : Int) (28288000000 : Int)
    geometryRow029_meanGap_numerator_no_slash geometryRow029_meanGap_numerator_parse
    geometryRow029_meanGap_denominator_parse geometryRow029_meanGap_denominator_nonzero

theorem geometryRow029_meanGap_read :
    rationalField geometryRowsJson029 "mean_gap" = .ok geometryRowsTyped029.meanGap :=
  original_rationalField_of_string geometryRowsJson029 "mean_gap" geometryRow029_meanGapText
    geometryRowsTyped029.meanGap geometryRow029_meanGap_field geometryRow029_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_meanGap_complete"
  err.flush

noncomputable def geometryRow029_jensenBoundNumeratorChars : List Char := ['2', '8', '0', '2', '8', '7', '9', '4', '0', '4', '5', '6', '2', '8', '6', '4', '7', '8', '6', '8', '3', '6', '0', '5', '0', '8', '6', '1', '5', '8', '1', '0', '9', '7', '7', '2', '4', '9', '1', '9', '0', '0', '6', '6', '3', '1', '0', '3', '9', '1', '0', '6', '3', '0', '0', '4', '5', '3', '9', '1', '5', '3', '1', '6', '7', '7', '1', '1', '0', '6', '5', '8', '5', '3', '2', '6', '4', '4', '9', '2', '2', '0', '0', '9', '5', '8', '3', '1', '9', '6', '8', '6', '9', '2', '0', '6', '6', '9', '2', '5', '8', '0', '6', '7', '1', '6', '8', '2', '2', '9', '1', '3', '4', '5', '3', '7', '1', '9', '8', '8', '6', '4', '6', '3', '8', '8', '4', '9', '6', '7', '3', '3', '7', '1', '7', '6', '8', '4', '9', '5', '1', '9', '0', '4', '1', '6', '1', '5', '8', '1', '8', '5', '5', '6', '6', '6', '7', '9', '7', '3', '1', '2', '4', '0', '1', '7', '3', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_jensenBoundDenominatorChars : List Char := ['6', '4', '1', '3', '9', '4', '8', '9', '4', '5', '5', '5', '6', '0', '4', '5', '0', '4', '3', '1', '3', '7', '6', '8', '4', '4', '9', '4', '1', '1', '5', '3', '6', '7', '4', '1', '7', '5', '8', '8', '1', '3', '8', '5', '2', '5', '7', '6', '3', '0', '8', '3', '6', '0', '2', '2', '4', '5', '1', '7', '0', '4', '0', '1', '7', '8', '8', '8', '2', '2', '7', '3', '9', '7', '1', '4', '5', '8', '0', '3', '8', '8', '0', '1', '1', '3', '9', '9', '8', '4', '6', '8', '8', '4', '3', '9', '2', '1', '8', '5', '6', '4', '3', '1', '4', '9', '7', '0', '8', '2', '5', '1', '8', '8', '0', '4', '6', '1', '5', '6', '2', '8', '3', '9', '6', '1', '4', '6', '9', '9', '0', '5', '4', '2', '4', '8', '6', '9', '2', '0', '2', '5', '3', '2', '9', '7', '4', '1', '9', '3', '3', '2', '5', '0', '4', '1', '7', '1', '0', '1', '5', '7', '3', '6', '3', '7', '6', '6', '2', '7', '3', '7', '4', '3', '1', '7', '6', '8', '6', '8', '6', '8', '2', '3', '6', '2', '2', '7', '6', '2', '6', '2', '5', '0', '7', '0', '2', '7', '9', '5', '4', '0', '0', '5', '1']
noncomputable def geometryRow029_jensenBoundText : String := String.ofList (geometryRow029_jensenBoundNumeratorChars ++ '/' :: geometryRow029_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_jensenBound_before_field"
  err.flush

theorem geometryRow029_jensenBound_field :
    geometryRowsJson029.getObjVal? "jensen_bound" = .ok (.str geometryRow029_jensenBoundText) := by rfl

theorem geometryRow029_jensenBound_numerator_no_slash :
    geometryRow029_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow029_jensenBoundNumeratorChars = some (280287940456286478683605086158109772491900663103910630045391531677110658532644922009583196869206692580671682291345371988646388496733717684951904161581855666797312401735680000000000000000000000 : Int) := by decide +kernel

theorem geometryRow029_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow029_jensenBoundDenominatorChars = some (6413948945556045043137684494115367417588138525763083602245170401788822739714580388011399846884392185643149708251880461562839614699054248692025329741933250417101573637662737431768686823622762625070279540051 : Int) := by decide +kernel

theorem geometryRow029_jensenBound_denominator_nonzero : (6413948945556045043137684494115367417588138525763083602245170401788822739714580388011399846884392185643149708251880461562839614699054248692025329741933250417101573637662737431768686823622762625070279540051 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_jensenBound_parse :
    parseRational geometryRow029_jensenBoundText = .ok geometryRowsTyped029.jensenBound :=
  original_rational_fraction_of_chars geometryRow029_jensenBoundNumeratorChars geometryRow029_jensenBoundDenominatorChars
    (280287940456286478683605086158109772491900663103910630045391531677110658532644922009583196869206692580671682291345371988646388496733717684951904161581855666797312401735680000000000000000000000 : Int) (6413948945556045043137684494115367417588138525763083602245170401788822739714580388011399846884392185643149708251880461562839614699054248692025329741933250417101573637662737431768686823622762625070279540051 : Int)
    geometryRow029_jensenBound_numerator_no_slash geometryRow029_jensenBound_numerator_parse
    geometryRow029_jensenBound_denominator_parse geometryRow029_jensenBound_denominator_nonzero

theorem geometryRow029_jensenBound_read :
    rationalField geometryRowsJson029 "jensen_bound" = .ok geometryRowsTyped029.jensenBound :=
  original_rationalField_of_string geometryRowsJson029 "jensen_bound" geometryRow029_jensenBoundText
    geometryRowsTyped029.jensenBound geometryRow029_jensenBound_field geometryRow029_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_factorMaxima_before"
  err.flush

theorem geometryRow029_factorMaxima_read :
    rationalArrayField geometryRowsJson029 "factor_maxima" = .ok geometryRowsTyped029.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_gapWeightedMeans_before"
  err.flush

theorem geometryRow029_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson029 "gap_weighted_means" = .ok geometryRowsTyped029.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow029_floorChars : List Char := ['3', '4', '6', '2', '2', '5', '0', '5', '8', '6', '3', '0', '1', '4', '6', '9']
noncomputable def geometryRow029_floorText : String := String.ofList geometryRow029_floorChars

theorem geometryRow029_floor_text_read :
    geometryRowsJson029.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow029_floorText := by rfl

theorem geometryRow029_floor_chars_parse :
    SourceJson.intChars geometryRow029_floorChars = some (3462250586301469 : Int) := by decide +kernel

theorem geometryRow029_floor_parse :
    parseInteger geometryRow029_floorText = .ok geometryRowsTyped029.jensenFloorQ96 := by
  simp only [geometryRow029_floorText, parseInteger, String.toList_ofList, geometryRow029_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_029 :
    decodeGeometryRow geometryRowsJson029 = .ok geometryRowsTyped029 :=
  original_geometryRow_of_fields geometryRowsJson029 geometryRowsTyped029 geometryRow029_floorText
    geometryRow029_simplexId_read geometryRow029_vertexIds_read
    geometryRow029_physicalVolume_read geometryRow029_meanGap_read
    geometryRow029_factorMaxima_read geometryRow029_gapWeightedMeans_read
    geometryRow029_jensenBound_read geometryRow029_floor_text_read geometryRow029_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_029_original_decoder_complete"
  err.flush

theorem geometryRow029_shape :
    geometryRowsTyped029.simplexId = 29 ∧
    geometryRowsTyped029.vertexIds.size = 9 ∧ geometryRowsTyped029.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped029.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped029.factorMaxima.size = 10 ∧ geometryRowsTyped029.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson030 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped030 : GeometryRow :=
  { simplexId := 30,
    vertexIds := #[27, 25, 23, 21, 19, 17, 15, 14, 4],
    physicalVolume := ((208374482089420035741705957657112213 : ℚ) / (29875650187500000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((321874867 : ℚ) / (424320000000 : ℚ)),
    factorMaxima := #[((2409379 : ℚ) / (25600000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2390621 : ℚ) / (32000000 : ℚ)), ((515593 : ℚ) / (12000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((174064611618921835981217 : ℚ) / (2026133792793302400000000 : ℚ)), ((1691470551132946685101 : ℚ) / (19482055699935600000000 : ℚ)), ((126734670635285107876963 : ℚ) / (1013066896396651200000000 : ℚ)), ((49281483031597859408063 : ℚ) / (506533448198325600000000 : ℚ)), ((47203621809095546279461 : ℚ) / (506533448198325600000000 : ℚ)), ((6905883018612926870879 : ℚ) / (101306689639665120000000 : ℚ)), ((2157126762063332921101 : ℚ) / (59592170376273600000000 : ℚ)), ((10494515598305048136371 : ℚ) / (337688965465550400000000 : ℚ)), ((780959593384412221567 : ℚ) / (25976074266580800000000 : ℚ)), ((192449079517864113029 : ℚ) / (6494018566645200000000 : ℚ))],
    jensenBound := ((626885474658920208573121736470041522859445763075126829915986604797063950536310443623193755438959046817878767942122102942482515140752422807923868608836302379672815070368321821999104000000000000000000000 : ℚ) / (17121826933746254090828558425601737212076217204097687711920718939834961018167083670481710840210295273035440109209988104463879395656152708287817547900489480331316739199665991145897488900796525836773184076586888448969 : ℚ)),
    jensenFloorQ96 := (2900799339714008 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_simplexId_before"
  err.flush

theorem geometryRow030_simplexId_read :
    geometryRowsJson030.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped030.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_vertexIds_before"
  err.flush

theorem geometryRow030_vertexIds_read :
    geometryRowsJson030.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped030.vertexIds := by decide +kernel

noncomputable def geometryRow030_physicalVolumeNumeratorChars : List Char := ['2', '0', '8', '3', '7', '4', '4', '8', '2', '0', '8', '9', '4', '2', '0', '0', '3', '5', '7', '4', '1', '7', '0', '5', '9', '5', '7', '6', '5', '7', '1', '1', '2', '2', '1', '3']
noncomputable def geometryRow030_physicalVolumeDenominatorChars : List Char := ['2', '9', '8', '7', '5', '6', '5', '0', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_physicalVolumeText : String := String.ofList (geometryRow030_physicalVolumeNumeratorChars ++ '/' :: geometryRow030_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_physicalVolume_before_field"
  err.flush

theorem geometryRow030_physicalVolume_field :
    geometryRowsJson030.getObjVal? "physical_volume" = .ok (.str geometryRow030_physicalVolumeText) := by rfl

theorem geometryRow030_physicalVolume_numerator_no_slash :
    geometryRow030_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow030_physicalVolumeNumeratorChars = some (208374482089420035741705957657112213 : Int) := by decide +kernel

theorem geometryRow030_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow030_physicalVolumeDenominatorChars = some (29875650187500000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow030_physicalVolume_denominator_nonzero : (29875650187500000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_physicalVolume_parse :
    parseRational geometryRow030_physicalVolumeText = .ok geometryRowsTyped030.physicalVolume :=
  original_rational_fraction_of_chars geometryRow030_physicalVolumeNumeratorChars geometryRow030_physicalVolumeDenominatorChars
    (208374482089420035741705957657112213 : Int) (29875650187500000000000000000000000000000000000000000000000 : Int)
    geometryRow030_physicalVolume_numerator_no_slash geometryRow030_physicalVolume_numerator_parse
    geometryRow030_physicalVolume_denominator_parse geometryRow030_physicalVolume_denominator_nonzero

theorem geometryRow030_physicalVolume_read :
    rationalField geometryRowsJson030 "physical_volume" = .ok geometryRowsTyped030.physicalVolume :=
  original_rationalField_of_string geometryRowsJson030 "physical_volume" geometryRow030_physicalVolumeText
    geometryRowsTyped030.physicalVolume geometryRow030_physicalVolume_field geometryRow030_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_physicalVolume_complete"
  err.flush

noncomputable def geometryRow030_meanGapNumeratorChars : List Char := ['3', '2', '1', '8', '7', '4', '8', '6', '7']
noncomputable def geometryRow030_meanGapDenominatorChars : List Char := ['4', '2', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_meanGapText : String := String.ofList (geometryRow030_meanGapNumeratorChars ++ '/' :: geometryRow030_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_meanGap_before_field"
  err.flush

theorem geometryRow030_meanGap_field :
    geometryRowsJson030.getObjVal? "mean_gap" = .ok (.str geometryRow030_meanGapText) := by rfl

theorem geometryRow030_meanGap_numerator_no_slash :
    geometryRow030_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_meanGap_numerator_parse :
    SourceJson.intChars geometryRow030_meanGapNumeratorChars = some (321874867 : Int) := by decide +kernel

theorem geometryRow030_meanGap_denominator_parse :
    SourceJson.intChars geometryRow030_meanGapDenominatorChars = some (424320000000 : Int) := by decide +kernel

theorem geometryRow030_meanGap_denominator_nonzero : (424320000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_meanGap_parse :
    parseRational geometryRow030_meanGapText = .ok geometryRowsTyped030.meanGap :=
  original_rational_fraction_of_chars geometryRow030_meanGapNumeratorChars geometryRow030_meanGapDenominatorChars
    (321874867 : Int) (424320000000 : Int)
    geometryRow030_meanGap_numerator_no_slash geometryRow030_meanGap_numerator_parse
    geometryRow030_meanGap_denominator_parse geometryRow030_meanGap_denominator_nonzero

theorem geometryRow030_meanGap_read :
    rationalField geometryRowsJson030 "mean_gap" = .ok geometryRowsTyped030.meanGap :=
  original_rationalField_of_string geometryRowsJson030 "mean_gap" geometryRow030_meanGapText
    geometryRowsTyped030.meanGap geometryRow030_meanGap_field geometryRow030_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_meanGap_complete"
  err.flush

noncomputable def geometryRow030_jensenBoundNumeratorChars : List Char := ['6', '2', '6', '8', '8', '5', '4', '7', '4', '6', '5', '8', '9', '2', '0', '2', '0', '8', '5', '7', '3', '1', '2', '1', '7', '3', '6', '4', '7', '0', '0', '4', '1', '5', '2', '2', '8', '5', '9', '4', '4', '5', '7', '6', '3', '0', '7', '5', '1', '2', '6', '8', '2', '9', '9', '1', '5', '9', '8', '6', '6', '0', '4', '7', '9', '7', '0', '6', '3', '9', '5', '0', '5', '3', '6', '3', '1', '0', '4', '4', '3', '6', '2', '3', '1', '9', '3', '7', '5', '5', '4', '3', '8', '9', '5', '9', '0', '4', '6', '8', '1', '7', '8', '7', '8', '7', '6', '7', '9', '4', '2', '1', '2', '2', '1', '0', '2', '9', '4', '2', '4', '8', '2', '5', '1', '5', '1', '4', '0', '7', '5', '2', '4', '2', '2', '8', '0', '7', '9', '2', '3', '8', '6', '8', '6', '0', '8', '8', '3', '6', '3', '0', '2', '3', '7', '9', '6', '7', '2', '8', '1', '5', '0', '7', '0', '3', '6', '8', '3', '2', '1', '8', '2', '1', '9', '9', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_jensenBoundDenominatorChars : List Char := ['1', '7', '1', '2', '1', '8', '2', '6', '9', '3', '3', '7', '4', '6', '2', '5', '4', '0', '9', '0', '8', '2', '8', '5', '5', '8', '4', '2', '5', '6', '0', '1', '7', '3', '7', '2', '1', '2', '0', '7', '6', '2', '1', '7', '2', '0', '4', '0', '9', '7', '6', '8', '7', '7', '1', '1', '9', '2', '0', '7', '1', '8', '9', '3', '9', '8', '3', '4', '9', '6', '1', '0', '1', '8', '1', '6', '7', '0', '8', '3', '6', '7', '0', '4', '8', '1', '7', '1', '0', '8', '4', '0', '2', '1', '0', '2', '9', '5', '2', '7', '3', '0', '3', '5', '4', '4', '0', '1', '0', '9', '2', '0', '9', '9', '8', '8', '1', '0', '4', '4', '6', '3', '8', '7', '9', '3', '9', '5', '6', '5', '6', '1', '5', '2', '7', '0', '8', '2', '8', '7', '8', '1', '7', '5', '4', '7', '9', '0', '0', '4', '8', '9', '4', '8', '0', '3', '3', '1', '3', '1', '6', '7', '3', '9', '1', '9', '9', '6', '6', '5', '9', '9', '1', '1', '4', '5', '8', '9', '7', '4', '8', '8', '9', '0', '0', '7', '9', '6', '5', '2', '5', '8', '3', '6', '7', '7', '3', '1', '8', '4', '0', '7', '6', '5', '8', '6', '8', '8', '8', '4', '4', '8', '9', '6', '9']
noncomputable def geometryRow030_jensenBoundText : String := String.ofList (geometryRow030_jensenBoundNumeratorChars ++ '/' :: geometryRow030_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_jensenBound_before_field"
  err.flush

theorem geometryRow030_jensenBound_field :
    geometryRowsJson030.getObjVal? "jensen_bound" = .ok (.str geometryRow030_jensenBoundText) := by rfl

theorem geometryRow030_jensenBound_numerator_no_slash :
    geometryRow030_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow030_jensenBoundNumeratorChars = some (626885474658920208573121736470041522859445763075126829915986604797063950536310443623193755438959046817878767942122102942482515140752422807923868608836302379672815070368321821999104000000000000000000000 : Int) := by decide +kernel

theorem geometryRow030_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow030_jensenBoundDenominatorChars = some (17121826933746254090828558425601737212076217204097687711920718939834961018167083670481710840210295273035440109209988104463879395656152708287817547900489480331316739199665991145897488900796525836773184076586888448969 : Int) := by decide +kernel

theorem geometryRow030_jensenBound_denominator_nonzero : (17121826933746254090828558425601737212076217204097687711920718939834961018167083670481710840210295273035440109209988104463879395656152708287817547900489480331316739199665991145897488900796525836773184076586888448969 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_jensenBound_parse :
    parseRational geometryRow030_jensenBoundText = .ok geometryRowsTyped030.jensenBound :=
  original_rational_fraction_of_chars geometryRow030_jensenBoundNumeratorChars geometryRow030_jensenBoundDenominatorChars
    (626885474658920208573121736470041522859445763075126829915986604797063950536310443623193755438959046817878767942122102942482515140752422807923868608836302379672815070368321821999104000000000000000000000 : Int) (17121826933746254090828558425601737212076217204097687711920718939834961018167083670481710840210295273035440109209988104463879395656152708287817547900489480331316739199665991145897488900796525836773184076586888448969 : Int)
    geometryRow030_jensenBound_numerator_no_slash geometryRow030_jensenBound_numerator_parse
    geometryRow030_jensenBound_denominator_parse geometryRow030_jensenBound_denominator_nonzero

theorem geometryRow030_jensenBound_read :
    rationalField geometryRowsJson030 "jensen_bound" = .ok geometryRowsTyped030.jensenBound :=
  original_rationalField_of_string geometryRowsJson030 "jensen_bound" geometryRow030_jensenBoundText
    geometryRowsTyped030.jensenBound geometryRow030_jensenBound_field geometryRow030_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_factorMaxima_before"
  err.flush

theorem geometryRow030_factorMaxima_read :
    rationalArrayField geometryRowsJson030 "factor_maxima" = .ok geometryRowsTyped030.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_gapWeightedMeans_before"
  err.flush

theorem geometryRow030_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson030 "gap_weighted_means" = .ok geometryRowsTyped030.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow030_floorChars : List Char := ['2', '9', '0', '0', '7', '9', '9', '3', '3', '9', '7', '1', '4', '0', '0', '8']
noncomputable def geometryRow030_floorText : String := String.ofList geometryRow030_floorChars

theorem geometryRow030_floor_text_read :
    geometryRowsJson030.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow030_floorText := by rfl

theorem geometryRow030_floor_chars_parse :
    SourceJson.intChars geometryRow030_floorChars = some (2900799339714008 : Int) := by decide +kernel

theorem geometryRow030_floor_parse :
    parseInteger geometryRow030_floorText = .ok geometryRowsTyped030.jensenFloorQ96 := by
  simp only [geometryRow030_floorText, parseInteger, String.toList_ofList, geometryRow030_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_030 :
    decodeGeometryRow geometryRowsJson030 = .ok geometryRowsTyped030 :=
  original_geometryRow_of_fields geometryRowsJson030 geometryRowsTyped030 geometryRow030_floorText
    geometryRow030_simplexId_read geometryRow030_vertexIds_read
    geometryRow030_physicalVolume_read geometryRow030_meanGap_read
    geometryRow030_factorMaxima_read geometryRow030_gapWeightedMeans_read
    geometryRow030_jensenBound_read geometryRow030_floor_text_read geometryRow030_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_030_original_decoder_complete"
  err.flush

theorem geometryRow030_shape :
    geometryRowsTyped030.simplexId = 30 ∧
    geometryRowsTyped030.vertexIds.size = 9 ∧ geometryRowsTyped030.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped030.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped030.factorMaxima.size = 10 ∧ geometryRowsTyped030.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson031 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped031 : GeometryRow :=
  { simplexId := 31,
    vertexIds := #[27, 25, 23, 21, 19, 18, 6, 4, 0],
    physicalVolume := ((63624682808153769623506844926287317 : ℚ) / (1867340790000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2531241 : ℚ) / (26500000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((34533781639125641 : ℚ) / (390988886400000000 : ℚ)), ((4341771117710857 : ℚ) / (48873610800000000 : ℚ)), ((4807247605871399 : ℚ) / (39098888640000000 : ℚ)), ((9156141580961147 : ℚ) / (97747221600000000 : ℚ)), ((8786024820146353 : ℚ) / (97747221600000000 : ℚ)), ((1379288015465243 : ℚ) / (19549444320000000 : ℚ)), ((7317065493834989 : ℚ) / (195494443200000000 : ℚ)), ((2100447462247627 : ℚ) / (65164814400000000 : ℚ)), ((2046099282252427 : ℚ) / (65164814400000000 : ℚ)), ((493727763240193 : ℚ) / (16291203600000000 : ℚ))],
    jensenBound := ((73241249633848969978746594307165616034858200605510367859723454168820290422783899215817001111867667858030512696999070924800000000000000000000000 : ℚ) / (1241739399916663207589830029595345157631761844296039217024525867597770642137497346700941367385351344492465619924614447103570984893808350433002357192465310827 : ℚ)),
    jensenFloorQ96 := (4673097776496284 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_simplexId_before"
  err.flush

theorem geometryRow031_simplexId_read :
    geometryRowsJson031.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped031.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_vertexIds_before"
  err.flush

theorem geometryRow031_vertexIds_read :
    geometryRowsJson031.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped031.vertexIds := by decide +kernel

noncomputable def geometryRow031_physicalVolumeNumeratorChars : List Char := ['6', '3', '6', '2', '4', '6', '8', '2', '8', '0', '8', '1', '5', '3', '7', '6', '9', '6', '2', '3', '5', '0', '6', '8', '4', '4', '9', '2', '6', '2', '8', '7', '3', '1', '7']
noncomputable def geometryRow031_physicalVolumeDenominatorChars : List Char := ['1', '8', '6', '7', '3', '4', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow031_physicalVolumeText : String := String.ofList (geometryRow031_physicalVolumeNumeratorChars ++ '/' :: geometryRow031_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_physicalVolume_before_field"
  err.flush

theorem geometryRow031_physicalVolume_field :
    geometryRowsJson031.getObjVal? "physical_volume" = .ok (.str geometryRow031_physicalVolumeText) := by rfl

theorem geometryRow031_physicalVolume_numerator_no_slash :
    geometryRow031_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow031_physicalVolumeNumeratorChars = some (63624682808153769623506844926287317 : Int) := by decide +kernel

theorem geometryRow031_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow031_physicalVolumeDenominatorChars = some (1867340790000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow031_physicalVolume_denominator_nonzero : (1867340790000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_physicalVolume_parse :
    parseRational geometryRow031_physicalVolumeText = .ok geometryRowsTyped031.physicalVolume :=
  original_rational_fraction_of_chars geometryRow031_physicalVolumeNumeratorChars geometryRow031_physicalVolumeDenominatorChars
    (63624682808153769623506844926287317 : Int) (1867340790000000000000000000000000000000000000000000000000 : Int)
    geometryRow031_physicalVolume_numerator_no_slash geometryRow031_physicalVolume_numerator_parse
    geometryRow031_physicalVolume_denominator_parse geometryRow031_physicalVolume_denominator_nonzero

theorem geometryRow031_physicalVolume_read :
    rationalField geometryRowsJson031 "physical_volume" = .ok geometryRowsTyped031.physicalVolume :=
  original_rationalField_of_string geometryRowsJson031 "physical_volume" geometryRow031_physicalVolumeText
    geometryRowsTyped031.physicalVolume geometryRow031_physicalVolume_field geometryRow031_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_physicalVolume_complete"
  err.flush

noncomputable def geometryRow031_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow031_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow031_meanGapText : String := String.ofList (geometryRow031_meanGapNumeratorChars ++ '/' :: geometryRow031_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_meanGap_before_field"
  err.flush

theorem geometryRow031_meanGap_field :
    geometryRowsJson031.getObjVal? "mean_gap" = .ok (.str geometryRow031_meanGapText) := by rfl

theorem geometryRow031_meanGap_numerator_no_slash :
    geometryRow031_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_meanGap_numerator_parse :
    SourceJson.intChars geometryRow031_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow031_meanGap_denominator_parse :
    SourceJson.intChars geometryRow031_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow031_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_meanGap_parse :
    parseRational geometryRow031_meanGapText = .ok geometryRowsTyped031.meanGap :=
  original_rational_fraction_of_chars geometryRow031_meanGapNumeratorChars geometryRow031_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow031_meanGap_numerator_no_slash geometryRow031_meanGap_numerator_parse
    geometryRow031_meanGap_denominator_parse geometryRow031_meanGap_denominator_nonzero

theorem geometryRow031_meanGap_read :
    rationalField geometryRowsJson031 "mean_gap" = .ok geometryRowsTyped031.meanGap :=
  original_rationalField_of_string geometryRowsJson031 "mean_gap" geometryRow031_meanGapText
    geometryRowsTyped031.meanGap geometryRow031_meanGap_field geometryRow031_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_meanGap_complete"
  err.flush

noncomputable def geometryRow031_jensenBoundNumeratorChars : List Char := ['7', '3', '2', '4', '1', '2', '4', '9', '6', '3', '3', '8', '4', '8', '9', '6', '9', '9', '7', '8', '7', '4', '6', '5', '9', '4', '3', '0', '7', '1', '6', '5', '6', '1', '6', '0', '3', '4', '8', '5', '8', '2', '0', '0', '6', '0', '5', '5', '1', '0', '3', '6', '7', '8', '5', '9', '7', '2', '3', '4', '5', '4', '1', '6', '8', '8', '2', '0', '2', '9', '0', '4', '2', '2', '7', '8', '3', '8', '9', '9', '2', '1', '5', '8', '1', '7', '0', '0', '1', '1', '1', '1', '8', '6', '7', '6', '6', '7', '8', '5', '8', '0', '3', '0', '5', '1', '2', '6', '9', '6', '9', '9', '9', '0', '7', '0', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow031_jensenBoundDenominatorChars : List Char := ['1', '2', '4', '1', '7', '3', '9', '3', '9', '9', '9', '1', '6', '6', '6', '3', '2', '0', '7', '5', '8', '9', '8', '3', '0', '0', '2', '9', '5', '9', '5', '3', '4', '5', '1', '5', '7', '6', '3', '1', '7', '6', '1', '8', '4', '4', '2', '9', '6', '0', '3', '9', '2', '1', '7', '0', '2', '4', '5', '2', '5', '8', '6', '7', '5', '9', '7', '7', '7', '0', '6', '4', '2', '1', '3', '7', '4', '9', '7', '3', '4', '6', '7', '0', '0', '9', '4', '1', '3', '6', '7', '3', '8', '5', '3', '5', '1', '3', '4', '4', '4', '9', '2', '4', '6', '5', '6', '1', '9', '9', '2', '4', '6', '1', '4', '4', '4', '7', '1', '0', '3', '5', '7', '0', '9', '8', '4', '8', '9', '3', '8', '0', '8', '3', '5', '0', '4', '3', '3', '0', '0', '2', '3', '5', '7', '1', '9', '2', '4', '6', '5', '3', '1', '0', '8', '2', '7']
noncomputable def geometryRow031_jensenBoundText : String := String.ofList (geometryRow031_jensenBoundNumeratorChars ++ '/' :: geometryRow031_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_jensenBound_before_field"
  err.flush

theorem geometryRow031_jensenBound_field :
    geometryRowsJson031.getObjVal? "jensen_bound" = .ok (.str geometryRow031_jensenBoundText) := by rfl

theorem geometryRow031_jensenBound_numerator_no_slash :
    geometryRow031_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow031_jensenBoundNumeratorChars = some (73241249633848969978746594307165616034858200605510367859723454168820290422783899215817001111867667858030512696999070924800000000000000000000000 : Int) := by decide +kernel

theorem geometryRow031_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow031_jensenBoundDenominatorChars = some (1241739399916663207589830029595345157631761844296039217024525867597770642137497346700941367385351344492465619924614447103570984893808350433002357192465310827 : Int) := by decide +kernel

theorem geometryRow031_jensenBound_denominator_nonzero : (1241739399916663207589830029595345157631761844296039217024525867597770642137497346700941367385351344492465619924614447103570984893808350433002357192465310827 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_jensenBound_parse :
    parseRational geometryRow031_jensenBoundText = .ok geometryRowsTyped031.jensenBound :=
  original_rational_fraction_of_chars geometryRow031_jensenBoundNumeratorChars geometryRow031_jensenBoundDenominatorChars
    (73241249633848969978746594307165616034858200605510367859723454168820290422783899215817001111867667858030512696999070924800000000000000000000000 : Int) (1241739399916663207589830029595345157631761844296039217024525867597770642137497346700941367385351344492465619924614447103570984893808350433002357192465310827 : Int)
    geometryRow031_jensenBound_numerator_no_slash geometryRow031_jensenBound_numerator_parse
    geometryRow031_jensenBound_denominator_parse geometryRow031_jensenBound_denominator_nonzero

theorem geometryRow031_jensenBound_read :
    rationalField geometryRowsJson031 "jensen_bound" = .ok geometryRowsTyped031.jensenBound :=
  original_rationalField_of_string geometryRowsJson031 "jensen_bound" geometryRow031_jensenBoundText
    geometryRowsTyped031.jensenBound geometryRow031_jensenBound_field geometryRow031_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_factorMaxima_before"
  err.flush

theorem geometryRow031_factorMaxima_read :
    rationalArrayField geometryRowsJson031 "factor_maxima" = .ok geometryRowsTyped031.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_gapWeightedMeans_before"
  err.flush

theorem geometryRow031_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson031 "gap_weighted_means" = .ok geometryRowsTyped031.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow031_floorChars : List Char := ['4', '6', '7', '3', '0', '9', '7', '7', '7', '6', '4', '9', '6', '2', '8', '4']
noncomputable def geometryRow031_floorText : String := String.ofList geometryRow031_floorChars

theorem geometryRow031_floor_text_read :
    geometryRowsJson031.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow031_floorText := by rfl

theorem geometryRow031_floor_chars_parse :
    SourceJson.intChars geometryRow031_floorChars = some (4673097776496284 : Int) := by decide +kernel

theorem geometryRow031_floor_parse :
    parseInteger geometryRow031_floorText = .ok geometryRowsTyped031.jensenFloorQ96 := by
  simp only [geometryRow031_floorText, parseInteger, String.toList_ofList, geometryRow031_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_031 :
    decodeGeometryRow geometryRowsJson031 = .ok geometryRowsTyped031 :=
  original_geometryRow_of_fields geometryRowsJson031 geometryRowsTyped031 geometryRow031_floorText
    geometryRow031_simplexId_read geometryRow031_vertexIds_read
    geometryRow031_physicalVolume_read geometryRow031_meanGap_read
    geometryRow031_factorMaxima_read geometryRow031_gapWeightedMeans_read
    geometryRow031_jensenBound_read geometryRow031_floor_text_read geometryRow031_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_031_original_decoder_complete"
  err.flush

theorem geometryRow031_shape :
    geometryRowsTyped031.simplexId = 31 ∧
    geometryRowsTyped031.vertexIds.size = 9 ∧ geometryRowsTyped031.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped031.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped031.factorMaxima.size = 10 ∧ geometryRowsTyped031.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock003 : List SourceJson := [geometryRowsJson024, geometryRowsJson025, geometryRowsJson026, geometryRowsJson027, geometryRowsJson028, geometryRowsJson029, geometryRowsJson030, geometryRowsJson031]
noncomputable def geometryRowsTypedBlock003 : List GeometryRow := [geometryRowsTyped024, geometryRowsTyped025, geometryRowsTyped026, geometryRowsTyped027, geometryRowsTyped028, geometryRowsTyped029, geometryRowsTyped030, geometryRowsTyped031]

theorem geometry_Rows_block_003_push_eq (acc : List SourceJson) :
    SimplicesBlock003.blockPush acc = [geometryRowsJson031, geometryRowsJson030, geometryRowsJson029, geometryRowsJson028, geometryRowsJson027, geometryRowsJson026, geometryRowsJson025, geometryRowsJson024] ++ acc := by rfl

theorem geometry_Rows_block_003_reverse (acc : List SourceJson) :
    (SimplicesBlock003.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock003 := by
  rw [geometry_Rows_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_003 :
    geometryRowsJsonBlock003.mapM decodeGeometryRow = .ok geometryRowsTypedBlock003 := by
  simp only [geometryRowsJsonBlock003, geometryRowsTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_024, decode_geometry_Rows_025, decode_geometry_Rows_026, decode_geometry_Rows_027, decode_geometry_Rows_028, decode_geometry_Rows_029, decode_geometry_Rows_030, decode_geometry_Rows_031]
  rfl

theorem geometry_Rows_block_003_length : geometryRowsTypedBlock003.length = 8 := by rfl

#print axioms geometryRow024_simplexId_read
#print axioms geometryRow024_vertexIds_read
#print axioms geometryRow024_physicalVolume_field
#print axioms geometryRow024_physicalVolume_numerator_no_slash
#print axioms geometryRow024_physicalVolume_numerator_parse
#print axioms geometryRow024_physicalVolume_denominator_parse
#print axioms geometryRow024_physicalVolume_denominator_nonzero
#print axioms geometryRow024_physicalVolume_parse
#print axioms geometryRow024_physicalVolume_read
#print axioms geometryRow024_meanGap_field
#print axioms geometryRow024_meanGap_numerator_no_slash
#print axioms geometryRow024_meanGap_numerator_parse
#print axioms geometryRow024_meanGap_denominator_parse
#print axioms geometryRow024_meanGap_denominator_nonzero
#print axioms geometryRow024_meanGap_parse
#print axioms geometryRow024_meanGap_read
#print axioms geometryRow024_jensenBound_field
#print axioms geometryRow024_jensenBound_numerator_no_slash
#print axioms geometryRow024_jensenBound_numerator_parse
#print axioms geometryRow024_jensenBound_denominator_parse
#print axioms geometryRow024_jensenBound_denominator_nonzero
#print axioms geometryRow024_jensenBound_parse
#print axioms geometryRow024_jensenBound_read
#print axioms geometryRow024_factorMaxima_read
#print axioms geometryRow024_gapWeightedMeans_read
#print axioms geometryRow024_floor_text_read
#print axioms geometryRow024_floor_chars_parse
#print axioms geometryRow024_floor_parse
#print axioms decode_geometry_Rows_024
#print axioms geometryRow024_shape
#print axioms geometryRow025_simplexId_read
#print axioms geometryRow025_vertexIds_read
#print axioms geometryRow025_physicalVolume_field
#print axioms geometryRow025_physicalVolume_numerator_no_slash
#print axioms geometryRow025_physicalVolume_numerator_parse
#print axioms geometryRow025_physicalVolume_denominator_parse
#print axioms geometryRow025_physicalVolume_denominator_nonzero
#print axioms geometryRow025_physicalVolume_parse
#print axioms geometryRow025_physicalVolume_read
#print axioms geometryRow025_meanGap_field
#print axioms geometryRow025_meanGap_numerator_no_slash
#print axioms geometryRow025_meanGap_numerator_parse
#print axioms geometryRow025_meanGap_denominator_parse
#print axioms geometryRow025_meanGap_denominator_nonzero
#print axioms geometryRow025_meanGap_parse
#print axioms geometryRow025_meanGap_read
#print axioms geometryRow025_jensenBound_field
#print axioms geometryRow025_jensenBound_numerator_no_slash
#print axioms geometryRow025_jensenBound_numerator_parse
#print axioms geometryRow025_jensenBound_denominator_parse
#print axioms geometryRow025_jensenBound_denominator_nonzero
#print axioms geometryRow025_jensenBound_parse
#print axioms geometryRow025_jensenBound_read
#print axioms geometryRow025_factorMaxima_read
#print axioms geometryRow025_gapWeightedMeans_read
#print axioms geometryRow025_floor_text_read
#print axioms geometryRow025_floor_chars_parse
#print axioms geometryRow025_floor_parse
#print axioms decode_geometry_Rows_025
#print axioms geometryRow025_shape
#print axioms geometryRow026_simplexId_read
#print axioms geometryRow026_vertexIds_read
#print axioms geometryRow026_physicalVolume_field
#print axioms geometryRow026_physicalVolume_numerator_no_slash
#print axioms geometryRow026_physicalVolume_numerator_parse
#print axioms geometryRow026_physicalVolume_denominator_parse
#print axioms geometryRow026_physicalVolume_denominator_nonzero
#print axioms geometryRow026_physicalVolume_parse
#print axioms geometryRow026_physicalVolume_read
#print axioms geometryRow026_meanGap_field
#print axioms geometryRow026_meanGap_numerator_no_slash
#print axioms geometryRow026_meanGap_numerator_parse
#print axioms geometryRow026_meanGap_denominator_parse
#print axioms geometryRow026_meanGap_denominator_nonzero
#print axioms geometryRow026_meanGap_parse
#print axioms geometryRow026_meanGap_read
#print axioms geometryRow026_jensenBound_field
#print axioms geometryRow026_jensenBound_numerator_no_slash
#print axioms geometryRow026_jensenBound_numerator_parse
#print axioms geometryRow026_jensenBound_denominator_parse
#print axioms geometryRow026_jensenBound_denominator_nonzero
#print axioms geometryRow026_jensenBound_parse
#print axioms geometryRow026_jensenBound_read
#print axioms geometryRow026_factorMaxima_read
#print axioms geometryRow026_gapWeightedMeans_read
#print axioms geometryRow026_floor_text_read
#print axioms geometryRow026_floor_chars_parse
#print axioms geometryRow026_floor_parse
#print axioms decode_geometry_Rows_026
#print axioms geometryRow026_shape
#print axioms geometryRow027_simplexId_read
#print axioms geometryRow027_vertexIds_read
#print axioms geometryRow027_physicalVolume_field
#print axioms geometryRow027_physicalVolume_numerator_no_slash
#print axioms geometryRow027_physicalVolume_numerator_parse
#print axioms geometryRow027_physicalVolume_denominator_parse
#print axioms geometryRow027_physicalVolume_denominator_nonzero
#print axioms geometryRow027_physicalVolume_parse
#print axioms geometryRow027_physicalVolume_read
#print axioms geometryRow027_meanGap_field
#print axioms geometryRow027_meanGap_numerator_no_slash
#print axioms geometryRow027_meanGap_numerator_parse
#print axioms geometryRow027_meanGap_denominator_parse
#print axioms geometryRow027_meanGap_denominator_nonzero
#print axioms geometryRow027_meanGap_parse
#print axioms geometryRow027_meanGap_read
#print axioms geometryRow027_jensenBound_field
#print axioms geometryRow027_jensenBound_numerator_no_slash
#print axioms geometryRow027_jensenBound_numerator_parse
#print axioms geometryRow027_jensenBound_denominator_parse
#print axioms geometryRow027_jensenBound_denominator_nonzero
#print axioms geometryRow027_jensenBound_parse
#print axioms geometryRow027_jensenBound_read
#print axioms geometryRow027_factorMaxima_read
#print axioms geometryRow027_gapWeightedMeans_read
#print axioms geometryRow027_floor_text_read
#print axioms geometryRow027_floor_chars_parse
#print axioms geometryRow027_floor_parse
#print axioms decode_geometry_Rows_027
#print axioms geometryRow027_shape
#print axioms geometryRow028_simplexId_read
#print axioms geometryRow028_vertexIds_read
#print axioms geometryRow028_physicalVolume_field
#print axioms geometryRow028_physicalVolume_numerator_no_slash
#print axioms geometryRow028_physicalVolume_numerator_parse
#print axioms geometryRow028_physicalVolume_denominator_parse
#print axioms geometryRow028_physicalVolume_denominator_nonzero
#print axioms geometryRow028_physicalVolume_parse
#print axioms geometryRow028_physicalVolume_read
#print axioms geometryRow028_meanGap_field
#print axioms geometryRow028_meanGap_numerator_no_slash
#print axioms geometryRow028_meanGap_numerator_parse
#print axioms geometryRow028_meanGap_denominator_parse
#print axioms geometryRow028_meanGap_denominator_nonzero
#print axioms geometryRow028_meanGap_parse
#print axioms geometryRow028_meanGap_read
#print axioms geometryRow028_jensenBound_field
#print axioms geometryRow028_jensenBound_numerator_no_slash
#print axioms geometryRow028_jensenBound_numerator_parse
#print axioms geometryRow028_jensenBound_denominator_parse
#print axioms geometryRow028_jensenBound_denominator_nonzero
#print axioms geometryRow028_jensenBound_parse
#print axioms geometryRow028_jensenBound_read
#print axioms geometryRow028_factorMaxima_read
#print axioms geometryRow028_gapWeightedMeans_read
#print axioms geometryRow028_floor_text_read
#print axioms geometryRow028_floor_chars_parse
#print axioms geometryRow028_floor_parse
#print axioms decode_geometry_Rows_028
#print axioms geometryRow028_shape
#print axioms geometryRow029_simplexId_read
#print axioms geometryRow029_vertexIds_read
#print axioms geometryRow029_physicalVolume_field
#print axioms geometryRow029_physicalVolume_numerator_no_slash
#print axioms geometryRow029_physicalVolume_numerator_parse
#print axioms geometryRow029_physicalVolume_denominator_parse
#print axioms geometryRow029_physicalVolume_denominator_nonzero
#print axioms geometryRow029_physicalVolume_parse
#print axioms geometryRow029_physicalVolume_read
#print axioms geometryRow029_meanGap_field
#print axioms geometryRow029_meanGap_numerator_no_slash
#print axioms geometryRow029_meanGap_numerator_parse
#print axioms geometryRow029_meanGap_denominator_parse
#print axioms geometryRow029_meanGap_denominator_nonzero
#print axioms geometryRow029_meanGap_parse
#print axioms geometryRow029_meanGap_read
#print axioms geometryRow029_jensenBound_field
#print axioms geometryRow029_jensenBound_numerator_no_slash
#print axioms geometryRow029_jensenBound_numerator_parse
#print axioms geometryRow029_jensenBound_denominator_parse
#print axioms geometryRow029_jensenBound_denominator_nonzero
#print axioms geometryRow029_jensenBound_parse
#print axioms geometryRow029_jensenBound_read
#print axioms geometryRow029_factorMaxima_read
#print axioms geometryRow029_gapWeightedMeans_read
#print axioms geometryRow029_floor_text_read
#print axioms geometryRow029_floor_chars_parse
#print axioms geometryRow029_floor_parse
#print axioms decode_geometry_Rows_029
#print axioms geometryRow029_shape
#print axioms geometryRow030_simplexId_read
#print axioms geometryRow030_vertexIds_read
#print axioms geometryRow030_physicalVolume_field
#print axioms geometryRow030_physicalVolume_numerator_no_slash
#print axioms geometryRow030_physicalVolume_numerator_parse
#print axioms geometryRow030_physicalVolume_denominator_parse
#print axioms geometryRow030_physicalVolume_denominator_nonzero
#print axioms geometryRow030_physicalVolume_parse
#print axioms geometryRow030_physicalVolume_read
#print axioms geometryRow030_meanGap_field
#print axioms geometryRow030_meanGap_numerator_no_slash
#print axioms geometryRow030_meanGap_numerator_parse
#print axioms geometryRow030_meanGap_denominator_parse
#print axioms geometryRow030_meanGap_denominator_nonzero
#print axioms geometryRow030_meanGap_parse
#print axioms geometryRow030_meanGap_read
#print axioms geometryRow030_jensenBound_field
#print axioms geometryRow030_jensenBound_numerator_no_slash
#print axioms geometryRow030_jensenBound_numerator_parse
#print axioms geometryRow030_jensenBound_denominator_parse
#print axioms geometryRow030_jensenBound_denominator_nonzero
#print axioms geometryRow030_jensenBound_parse
#print axioms geometryRow030_jensenBound_read
#print axioms geometryRow030_factorMaxima_read
#print axioms geometryRow030_gapWeightedMeans_read
#print axioms geometryRow030_floor_text_read
#print axioms geometryRow030_floor_chars_parse
#print axioms geometryRow030_floor_parse
#print axioms decode_geometry_Rows_030
#print axioms geometryRow030_shape
#print axioms geometryRow031_simplexId_read
#print axioms geometryRow031_vertexIds_read
#print axioms geometryRow031_physicalVolume_field
#print axioms geometryRow031_physicalVolume_numerator_no_slash
#print axioms geometryRow031_physicalVolume_numerator_parse
#print axioms geometryRow031_physicalVolume_denominator_parse
#print axioms geometryRow031_physicalVolume_denominator_nonzero
#print axioms geometryRow031_physicalVolume_parse
#print axioms geometryRow031_physicalVolume_read
#print axioms geometryRow031_meanGap_field
#print axioms geometryRow031_meanGap_numerator_no_slash
#print axioms geometryRow031_meanGap_numerator_parse
#print axioms geometryRow031_meanGap_denominator_parse
#print axioms geometryRow031_meanGap_denominator_nonzero
#print axioms geometryRow031_meanGap_parse
#print axioms geometryRow031_meanGap_read
#print axioms geometryRow031_jensenBound_field
#print axioms geometryRow031_jensenBound_numerator_no_slash
#print axioms geometryRow031_jensenBound_numerator_parse
#print axioms geometryRow031_jensenBound_denominator_parse
#print axioms geometryRow031_jensenBound_denominator_nonzero
#print axioms geometryRow031_jensenBound_parse
#print axioms geometryRow031_jensenBound_read
#print axioms geometryRow031_factorMaxima_read
#print axioms geometryRow031_gapWeightedMeans_read
#print axioms geometryRow031_floor_text_read
#print axioms geometryRow031_floor_chars_parse
#print axioms geometryRow031_floor_parse
#print axioms decode_geometry_Rows_031
#print axioms geometryRow031_shape
#print axioms geometry_Rows_block_003_push_eq
#print axioms geometry_Rows_block_003_reverse
#print axioms decode_geometry_Rows_block_003
#print axioms geometry_Rows_block_003_length

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
