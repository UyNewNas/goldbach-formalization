import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00400

/-! Original GeometryRow 17: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson017 : SourceJson :=
  (simplicesChunk017Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped017 : GeometryRow :=
  { simplexId := 17,
    vertexIds := #[27, 25, 23, 21, 19, 5, 4, 2, 0],
    physicalVolume := ((307982080108907272925444316244549883 : ℚ) / (2548803722308593750000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1640269 : ℚ) / (3744000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((1033946206613569 : ℚ) / (11365754400000000 : ℚ)), ((521454568355807 : ℚ) / (5682877200000000 : ℚ)), ((31175533824489 : ℚ) / (252572320000000 : ℚ)), ((81947707853849 : ℚ) / (874288800000000 : ℚ)), ((330152263950511 : ℚ) / (3788584800000000 : ℚ)), ((2500886416851 : ℚ) / (36081760000000 : ℚ)), ((2334232160969 : ℚ) / (67653300000000 : ℚ)), ((6833602922843 : ℚ) / (202959900000000 : ℚ)), ((45931837412621 : ℚ) / (1420719300000000 : ℚ)), ((177763705853429 : ℚ) / (5682877200000000 : ℚ))],
    jensenBound := ((175361998782918304523594461594336907568077556906203432063641903152660274682579046700703065399361536000000000000000000000000 : ℚ) / (567523138327697660522200636061646742895487281306850184557224935652954964521256903952782954547903495246679941158785353730160103001909589 : ℚ)),
    jensenFloorQ96 := (24481132133817717 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_simplexId_before"
  err.flush

theorem geometryRow017_simplexId_read :
    geometryRowsJson017.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped017.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_vertexIds_before"
  err.flush

theorem geometryRow017_vertexIds_read :
    geometryRowsJson017.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped017.vertexIds := by decide +kernel

noncomputable def geometryRow017_physicalVolumeNumeratorChars : List Char := ['3', '0', '7', '9', '8', '2', '0', '8', '0', '1', '0', '8', '9', '0', '7', '2', '7', '2', '9', '2', '5', '4', '4', '4', '3', '1', '6', '2', '4', '4', '5', '4', '9', '8', '8', '3']
noncomputable def geometryRow017_physicalVolumeDenominatorChars : List Char := ['2', '5', '4', '8', '8', '0', '3', '7', '2', '2', '3', '0', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow017_physicalVolumeText : String := String.ofList (geometryRow017_physicalVolumeNumeratorChars ++ '/' :: geometryRow017_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_physicalVolume_before_field"
  err.flush

theorem geometryRow017_physicalVolume_field :
    geometryRowsJson017.getObjVal? "physical_volume" = .ok (.str geometryRow017_physicalVolumeText) := by rfl

theorem geometryRow017_physicalVolume_numerator_no_slash :
    geometryRow017_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow017_physicalVolumeNumeratorChars = some (307982080108907272925444316244549883 : Int) := by decide +kernel

theorem geometryRow017_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow017_physicalVolumeDenominatorChars = some (2548803722308593750000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow017_physicalVolume_denominator_nonzero : (2548803722308593750000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_physicalVolume_parse :
    parseRational geometryRow017_physicalVolumeText = .ok geometryRowsTyped017.physicalVolume :=
  original_rational_fraction_of_chars geometryRow017_physicalVolumeNumeratorChars geometryRow017_physicalVolumeDenominatorChars
    (307982080108907272925444316244549883 : Int) (2548803722308593750000000000000000000000000000000000000000 : Int)
    geometryRow017_physicalVolume_numerator_no_slash geometryRow017_physicalVolume_numerator_parse
    geometryRow017_physicalVolume_denominator_parse geometryRow017_physicalVolume_denominator_nonzero

theorem geometryRow017_physicalVolume_read :
    rationalField geometryRowsJson017 "physical_volume" = .ok geometryRowsTyped017.physicalVolume :=
  original_rationalField_of_string geometryRowsJson017 "physical_volume" geometryRow017_physicalVolumeText
    geometryRowsTyped017.physicalVolume geometryRow017_physicalVolume_field geometryRow017_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_physicalVolume_complete"
  err.flush

noncomputable def geometryRow017_meanGapNumeratorChars : List Char := ['1', '6', '4', '0', '2', '6', '9']
noncomputable def geometryRow017_meanGapDenominatorChars : List Char := ['3', '7', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow017_meanGapText : String := String.ofList (geometryRow017_meanGapNumeratorChars ++ '/' :: geometryRow017_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_meanGap_before_field"
  err.flush

theorem geometryRow017_meanGap_field :
    geometryRowsJson017.getObjVal? "mean_gap" = .ok (.str geometryRow017_meanGapText) := by rfl

theorem geometryRow017_meanGap_numerator_no_slash :
    geometryRow017_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_meanGap_numerator_parse :
    SourceJson.intChars geometryRow017_meanGapNumeratorChars = some (1640269 : Int) := by decide +kernel

theorem geometryRow017_meanGap_denominator_parse :
    SourceJson.intChars geometryRow017_meanGapDenominatorChars = some (3744000000 : Int) := by decide +kernel

theorem geometryRow017_meanGap_denominator_nonzero : (3744000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_meanGap_parse :
    parseRational geometryRow017_meanGapText = .ok geometryRowsTyped017.meanGap :=
  original_rational_fraction_of_chars geometryRow017_meanGapNumeratorChars geometryRow017_meanGapDenominatorChars
    (1640269 : Int) (3744000000 : Int)
    geometryRow017_meanGap_numerator_no_slash geometryRow017_meanGap_numerator_parse
    geometryRow017_meanGap_denominator_parse geometryRow017_meanGap_denominator_nonzero

theorem geometryRow017_meanGap_read :
    rationalField geometryRowsJson017 "mean_gap" = .ok geometryRowsTyped017.meanGap :=
  original_rationalField_of_string geometryRowsJson017 "mean_gap" geometryRow017_meanGapText
    geometryRowsTyped017.meanGap geometryRow017_meanGap_field geometryRow017_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_meanGap_complete"
  err.flush

noncomputable def geometryRow017_jensenBoundNumeratorChars : List Char := ['1', '7', '5', '3', '6', '1', '9', '9', '8', '7', '8', '2', '9', '1', '8', '3', '0', '4', '5', '2', '3', '5', '9', '4', '4', '6', '1', '5', '9', '4', '3', '3', '6', '9', '0', '7', '5', '6', '8', '0', '7', '7', '5', '5', '6', '9', '0', '6', '2', '0', '3', '4', '3', '2', '0', '6', '3', '6', '4', '1', '9', '0', '3', '1', '5', '2', '6', '6', '0', '2', '7', '4', '6', '8', '2', '5', '7', '9', '0', '4', '6', '7', '0', '0', '7', '0', '3', '0', '6', '5', '3', '9', '9', '3', '6', '1', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow017_jensenBoundDenominatorChars : List Char := ['5', '6', '7', '5', '2', '3', '1', '3', '8', '3', '2', '7', '6', '9', '7', '6', '6', '0', '5', '2', '2', '2', '0', '0', '6', '3', '6', '0', '6', '1', '6', '4', '6', '7', '4', '2', '8', '9', '5', '4', '8', '7', '2', '8', '1', '3', '0', '6', '8', '5', '0', '1', '8', '4', '5', '5', '7', '2', '2', '4', '9', '3', '5', '6', '5', '2', '9', '5', '4', '9', '6', '4', '5', '2', '1', '2', '5', '6', '9', '0', '3', '9', '5', '2', '7', '8', '2', '9', '5', '4', '5', '4', '7', '9', '0', '3', '4', '9', '5', '2', '4', '6', '6', '7', '9', '9', '4', '1', '1', '5', '8', '7', '8', '5', '3', '5', '3', '7', '3', '0', '1', '6', '0', '1', '0', '3', '0', '0', '1', '9', '0', '9', '5', '8', '9']
noncomputable def geometryRow017_jensenBoundText : String := String.ofList (geometryRow017_jensenBoundNumeratorChars ++ '/' :: geometryRow017_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_jensenBound_before_field"
  err.flush

theorem geometryRow017_jensenBound_field :
    geometryRowsJson017.getObjVal? "jensen_bound" = .ok (.str geometryRow017_jensenBoundText) := by rfl

theorem geometryRow017_jensenBound_numerator_no_slash :
    geometryRow017_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow017_jensenBoundNumeratorChars = some (175361998782918304523594461594336907568077556906203432063641903152660274682579046700703065399361536000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow017_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow017_jensenBoundDenominatorChars = some (567523138327697660522200636061646742895487281306850184557224935652954964521256903952782954547903495246679941158785353730160103001909589 : Int) := by decide +kernel

theorem geometryRow017_jensenBound_denominator_nonzero : (567523138327697660522200636061646742895487281306850184557224935652954964521256903952782954547903495246679941158785353730160103001909589 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_jensenBound_parse :
    parseRational geometryRow017_jensenBoundText = .ok geometryRowsTyped017.jensenBound :=
  original_rational_fraction_of_chars geometryRow017_jensenBoundNumeratorChars geometryRow017_jensenBoundDenominatorChars
    (175361998782918304523594461594336907568077556906203432063641903152660274682579046700703065399361536000000000000000000000000 : Int) (567523138327697660522200636061646742895487281306850184557224935652954964521256903952782954547903495246679941158785353730160103001909589 : Int)
    geometryRow017_jensenBound_numerator_no_slash geometryRow017_jensenBound_numerator_parse
    geometryRow017_jensenBound_denominator_parse geometryRow017_jensenBound_denominator_nonzero

theorem geometryRow017_jensenBound_read :
    rationalField geometryRowsJson017 "jensen_bound" = .ok geometryRowsTyped017.jensenBound :=
  original_rationalField_of_string geometryRowsJson017 "jensen_bound" geometryRow017_jensenBoundText
    geometryRowsTyped017.jensenBound geometryRow017_jensenBound_field geometryRow017_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_factorMaxima_before"
  err.flush

theorem geometryRow017_factorMaxima_read :
    rationalArrayField geometryRowsJson017 "factor_maxima" = .ok geometryRowsTyped017.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_gapWeightedMeans_before"
  err.flush

theorem geometryRow017_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson017 "gap_weighted_means" = .ok geometryRowsTyped017.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow017_floorChars : List Char := ['2', '4', '4', '8', '1', '1', '3', '2', '1', '3', '3', '8', '1', '7', '7', '1', '7']
noncomputable def geometryRow017_floorText : String := String.ofList geometryRow017_floorChars

theorem geometryRow017_floor_text_read :
    geometryRowsJson017.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow017_floorText := by rfl

theorem geometryRow017_floor_chars_parse :
    SourceJson.intChars geometryRow017_floorChars = some (24481132133817717 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY00_TYPED Row_017_original_decoder_complete"
  err.flush

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

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
