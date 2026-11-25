import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00300

/-! Original GeometryRow 15: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson015 : SourceJson :=
  (simplicesChunk015Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped015 : GeometryRow :=
  { simplexId := 15,
    vertexIds := #[27, 25, 23, 21, 19, 5, 3, 1, 0],
    physicalVolume := ((876073686928825235575037305633 : ℚ) / (62383307888671875000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((1830517842557 : ℚ) / (19870200000000 : ℚ)), ((461203109573 : ℚ) / (4967550000000 : ℚ)), ((108835430097 : ℚ) / (883120000000 : ℚ)), ((3697386235457 : ℚ) / (39740400000000 : ℚ)), ((384861256217 : ℚ) / (4415600000000 : ℚ)), ((1767119821 : ℚ) / (25232000000 : ℚ)), ((16224936923 : ℚ) / (473100000000 : ℚ)), ((47492338321 : ℚ) / (1419300000000 : ℚ)), ((157184572511 : ℚ) / (4967550000000 : ℚ)), ((157183247831 : ℚ) / (4967550000000 : ℚ))],
    jensenBound := ((47858335862314105882403422053284558378671401297266038619313919749482086400000000000000000000000 : ℚ) / (1466233015051285789055463757415414314353371629977326803855168728754430886919803027570801331376075796502256346533 : ℚ)),
    jensenFloorQ96 := (2586033715267 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_simplexId_before"
  err.flush

theorem geometryRow015_simplexId_read :
    geometryRowsJson015.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped015.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_vertexIds_before"
  err.flush

theorem geometryRow015_vertexIds_read :
    geometryRowsJson015.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped015.vertexIds := by decide +kernel

noncomputable def geometryRow015_physicalVolumeNumeratorChars : List Char := ['8', '7', '6', '0', '7', '3', '6', '8', '6', '9', '2', '8', '8', '2', '5', '2', '3', '5', '5', '7', '5', '0', '3', '7', '3', '0', '5', '6', '3', '3']
noncomputable def geometryRow015_physicalVolumeDenominatorChars : List Char := ['6', '2', '3', '8', '3', '3', '0', '7', '8', '8', '8', '6', '7', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_physicalVolumeText : String := String.ofList (geometryRow015_physicalVolumeNumeratorChars ++ '/' :: geometryRow015_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_physicalVolume_before_field"
  err.flush

theorem geometryRow015_physicalVolume_field :
    geometryRowsJson015.getObjVal? "physical_volume" = .ok (.str geometryRow015_physicalVolumeText) := by rfl

theorem geometryRow015_physicalVolume_numerator_no_slash :
    geometryRow015_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow015_physicalVolumeNumeratorChars = some (876073686928825235575037305633 : Int) := by decide +kernel

theorem geometryRow015_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow015_physicalVolumeDenominatorChars = some (62383307888671875000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow015_physicalVolume_denominator_nonzero : (62383307888671875000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_physicalVolume_parse :
    parseRational geometryRow015_physicalVolumeText = .ok geometryRowsTyped015.physicalVolume :=
  original_rational_fraction_of_chars geometryRow015_physicalVolumeNumeratorChars geometryRow015_physicalVolumeDenominatorChars
    (876073686928825235575037305633 : Int) (62383307888671875000000000000000000000000000000000000000 : Int)
    geometryRow015_physicalVolume_numerator_no_slash geometryRow015_physicalVolume_numerator_parse
    geometryRow015_physicalVolume_denominator_parse geometryRow015_physicalVolume_denominator_nonzero

theorem geometryRow015_physicalVolume_read :
    rationalField geometryRowsJson015 "physical_volume" = .ok geometryRowsTyped015.physicalVolume :=
  original_rationalField_of_string geometryRowsJson015 "physical_volume" geometryRow015_physicalVolumeText
    geometryRowsTyped015.physicalVolume geometryRow015_physicalVolume_field geometryRow015_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_physicalVolume_complete"
  err.flush

noncomputable def geometryRow015_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow015_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_meanGapText : String := String.ofList (geometryRow015_meanGapNumeratorChars ++ '/' :: geometryRow015_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_meanGap_before_field"
  err.flush

theorem geometryRow015_meanGap_field :
    geometryRowsJson015.getObjVal? "mean_gap" = .ok (.str geometryRow015_meanGapText) := by rfl

theorem geometryRow015_meanGap_numerator_no_slash :
    geometryRow015_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_meanGap_numerator_parse :
    SourceJson.intChars geometryRow015_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow015_meanGap_denominator_parse :
    SourceJson.intChars geometryRow015_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow015_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_meanGap_parse :
    parseRational geometryRow015_meanGapText = .ok geometryRowsTyped015.meanGap :=
  original_rational_fraction_of_chars geometryRow015_meanGapNumeratorChars geometryRow015_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow015_meanGap_numerator_no_slash geometryRow015_meanGap_numerator_parse
    geometryRow015_meanGap_denominator_parse geometryRow015_meanGap_denominator_nonzero

theorem geometryRow015_meanGap_read :
    rationalField geometryRowsJson015 "mean_gap" = .ok geometryRowsTyped015.meanGap :=
  original_rationalField_of_string geometryRowsJson015 "mean_gap" geometryRow015_meanGapText
    geometryRowsTyped015.meanGap geometryRow015_meanGap_field geometryRow015_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_meanGap_complete"
  err.flush

noncomputable def geometryRow015_jensenBoundNumeratorChars : List Char := ['4', '7', '8', '5', '8', '3', '3', '5', '8', '6', '2', '3', '1', '4', '1', '0', '5', '8', '8', '2', '4', '0', '3', '4', '2', '2', '0', '5', '3', '2', '8', '4', '5', '5', '8', '3', '7', '8', '6', '7', '1', '4', '0', '1', '2', '9', '7', '2', '6', '6', '0', '3', '8', '6', '1', '9', '3', '1', '3', '9', '1', '9', '7', '4', '9', '4', '8', '2', '0', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_jensenBoundDenominatorChars : List Char := ['1', '4', '6', '6', '2', '3', '3', '0', '1', '5', '0', '5', '1', '2', '8', '5', '7', '8', '9', '0', '5', '5', '4', '6', '3', '7', '5', '7', '4', '1', '5', '4', '1', '4', '3', '1', '4', '3', '5', '3', '3', '7', '1', '6', '2', '9', '9', '7', '7', '3', '2', '6', '8', '0', '3', '8', '5', '5', '1', '6', '8', '7', '2', '8', '7', '5', '4', '4', '3', '0', '8', '8', '6', '9', '1', '9', '8', '0', '3', '0', '2', '7', '5', '7', '0', '8', '0', '1', '3', '3', '1', '3', '7', '6', '0', '7', '5', '7', '9', '6', '5', '0', '2', '2', '5', '6', '3', '4', '6', '5', '3', '3']
noncomputable def geometryRow015_jensenBoundText : String := String.ofList (geometryRow015_jensenBoundNumeratorChars ++ '/' :: geometryRow015_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_jensenBound_before_field"
  err.flush

theorem geometryRow015_jensenBound_field :
    geometryRowsJson015.getObjVal? "jensen_bound" = .ok (.str geometryRow015_jensenBoundText) := by rfl

theorem geometryRow015_jensenBound_numerator_no_slash :
    geometryRow015_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow015_jensenBoundNumeratorChars = some (47858335862314105882403422053284558378671401297266038619313919749482086400000000000000000000000 : Int) := by decide +kernel

theorem geometryRow015_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow015_jensenBoundDenominatorChars = some (1466233015051285789055463757415414314353371629977326803855168728754430886919803027570801331376075796502256346533 : Int) := by decide +kernel

theorem geometryRow015_jensenBound_denominator_nonzero : (1466233015051285789055463757415414314353371629977326803855168728754430886919803027570801331376075796502256346533 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_jensenBound_parse :
    parseRational geometryRow015_jensenBoundText = .ok geometryRowsTyped015.jensenBound :=
  original_rational_fraction_of_chars geometryRow015_jensenBoundNumeratorChars geometryRow015_jensenBoundDenominatorChars
    (47858335862314105882403422053284558378671401297266038619313919749482086400000000000000000000000 : Int) (1466233015051285789055463757415414314353371629977326803855168728754430886919803027570801331376075796502256346533 : Int)
    geometryRow015_jensenBound_numerator_no_slash geometryRow015_jensenBound_numerator_parse
    geometryRow015_jensenBound_denominator_parse geometryRow015_jensenBound_denominator_nonzero

theorem geometryRow015_jensenBound_read :
    rationalField geometryRowsJson015 "jensen_bound" = .ok geometryRowsTyped015.jensenBound :=
  original_rationalField_of_string geometryRowsJson015 "jensen_bound" geometryRow015_jensenBoundText
    geometryRowsTyped015.jensenBound geometryRow015_jensenBound_field geometryRow015_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_factorMaxima_before"
  err.flush

theorem geometryRow015_factorMaxima_read :
    rationalArrayField geometryRowsJson015 "factor_maxima" = .ok geometryRowsTyped015.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_gapWeightedMeans_before"
  err.flush

theorem geometryRow015_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson015 "gap_weighted_means" = .ok geometryRowsTyped015.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow015_floorChars : List Char := ['2', '5', '8', '6', '0', '3', '3', '7', '1', '5', '2', '6', '7']
noncomputable def geometryRow015_floorText : String := String.ofList geometryRow015_floorChars

theorem geometryRow015_floor_text_read :
    geometryRowsJson015.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow015_floorText := by rfl

theorem geometryRow015_floor_chars_parse :
    SourceJson.intChars geometryRow015_floorChars = some (2586033715267 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY00_TYPED Row_015_original_decoder_complete"
  err.flush

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

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
