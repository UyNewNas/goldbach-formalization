import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01100

/-! Original GeometryRow 45: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson045 : SourceJson :=
  (simplicesChunk045Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped045 : GeometryRow :=
  { simplexId := 45,
    vertexIds := #[27, 15, 11, 9, 7, 6, 5, 3, 1],
    physicalVolume := ((358323786338144184763259849417648365893037 : ℚ) / (6219902631385497600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1490621 : ℚ) / (16800000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((8227990093093 : ℚ) / (86104200000000 : ℚ)), ((4144966670639 : ℚ) / (43052100000000 : ℚ)), ((123845603746409 : ℚ) / (1033250400000000 : ℚ)), ((90291477132593 : ℚ) / (1033250400000000 : ℚ)), ((81626250950011 : ℚ) / (1033250400000000 : ℚ)), ((76132095833431 : ℚ) / (1033250400000000 : ℚ)), ((4752599367961 : ℚ) / (129156300000000 : ℚ)), ((9233594793557 : ℚ) / (258312600000000 : ℚ)), ((8996183955347 : ℚ) / (258312600000000 : ℚ)), ((243352993549 : ℚ) / (7175350000000 : ℚ))],
    jensenBound := ((829740046247140088608936682675453117279850525311533138461015068841564174757914682046279543132812500000000000000000 : ℚ) / (7851250455984971753917578674168053453476232607346019478272802426837781886228290932508701876337470002563780998772102205981157496001 : ℚ)),
    jensenFloorQ96 := (8373033008843 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_simplexId_before"
  err.flush

theorem geometryRow045_simplexId_read :
    geometryRowsJson045.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped045.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_vertexIds_before"
  err.flush

theorem geometryRow045_vertexIds_read :
    geometryRowsJson045.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped045.vertexIds := by decide +kernel

noncomputable def geometryRow045_physicalVolumeNumeratorChars : List Char := ['3', '5', '8', '3', '2', '3', '7', '8', '6', '3', '3', '8', '1', '4', '4', '1', '8', '4', '7', '6', '3', '2', '5', '9', '8', '4', '9', '4', '1', '7', '6', '4', '8', '3', '6', '5', '8', '9', '3', '0', '3', '7']
noncomputable def geometryRow045_physicalVolumeDenominatorChars : List Char := ['6', '2', '1', '9', '9', '0', '2', '6', '3', '1', '3', '8', '5', '4', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_physicalVolumeText : String := String.ofList (geometryRow045_physicalVolumeNumeratorChars ++ '/' :: geometryRow045_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_physicalVolume_before_field"
  err.flush

theorem geometryRow045_physicalVolume_field :
    geometryRowsJson045.getObjVal? "physical_volume" = .ok (.str geometryRow045_physicalVolumeText) := by rfl

theorem geometryRow045_physicalVolume_numerator_no_slash :
    geometryRow045_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow045_physicalVolumeNumeratorChars = some (358323786338144184763259849417648365893037 : Int) := by decide +kernel

theorem geometryRow045_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow045_physicalVolumeDenominatorChars = some (6219902631385497600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow045_physicalVolume_denominator_nonzero : (6219902631385497600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_physicalVolume_parse :
    parseRational geometryRow045_physicalVolumeText = .ok geometryRowsTyped045.physicalVolume :=
  original_rational_fraction_of_chars geometryRow045_physicalVolumeNumeratorChars geometryRow045_physicalVolumeDenominatorChars
    (358323786338144184763259849417648365893037 : Int) (6219902631385497600000000000000000000000000000000000000000000000000 : Int)
    geometryRow045_physicalVolume_numerator_no_slash geometryRow045_physicalVolume_numerator_parse
    geometryRow045_physicalVolume_denominator_parse geometryRow045_physicalVolume_denominator_nonzero

theorem geometryRow045_physicalVolume_read :
    rationalField geometryRowsJson045 "physical_volume" = .ok geometryRowsTyped045.physicalVolume :=
  original_rationalField_of_string geometryRowsJson045 "physical_volume" geometryRow045_physicalVolumeText
    geometryRowsTyped045.physicalVolume geometryRow045_physicalVolume_field geometryRow045_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_physicalVolume_complete"
  err.flush

noncomputable def geometryRow045_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow045_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_meanGapText : String := String.ofList (geometryRow045_meanGapNumeratorChars ++ '/' :: geometryRow045_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_meanGap_before_field"
  err.flush

theorem geometryRow045_meanGap_field :
    geometryRowsJson045.getObjVal? "mean_gap" = .ok (.str geometryRow045_meanGapText) := by rfl

theorem geometryRow045_meanGap_numerator_no_slash :
    geometryRow045_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_meanGap_numerator_parse :
    SourceJson.intChars geometryRow045_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow045_meanGap_denominator_parse :
    SourceJson.intChars geometryRow045_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow045_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_meanGap_parse :
    parseRational geometryRow045_meanGapText = .ok geometryRowsTyped045.meanGap :=
  original_rational_fraction_of_chars geometryRow045_meanGapNumeratorChars geometryRow045_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow045_meanGap_numerator_no_slash geometryRow045_meanGap_numerator_parse
    geometryRow045_meanGap_denominator_parse geometryRow045_meanGap_denominator_nonzero

theorem geometryRow045_meanGap_read :
    rationalField geometryRowsJson045 "mean_gap" = .ok geometryRowsTyped045.meanGap :=
  original_rationalField_of_string geometryRowsJson045 "mean_gap" geometryRow045_meanGapText
    geometryRowsTyped045.meanGap geometryRow045_meanGap_field geometryRow045_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_meanGap_complete"
  err.flush

noncomputable def geometryRow045_jensenBoundNumeratorChars : List Char := ['8', '2', '9', '7', '4', '0', '0', '4', '6', '2', '4', '7', '1', '4', '0', '0', '8', '8', '6', '0', '8', '9', '3', '6', '6', '8', '2', '6', '7', '5', '4', '5', '3', '1', '1', '7', '2', '7', '9', '8', '5', '0', '5', '2', '5', '3', '1', '1', '5', '3', '3', '1', '3', '8', '4', '6', '1', '0', '1', '5', '0', '6', '8', '8', '4', '1', '5', '6', '4', '1', '7', '4', '7', '5', '7', '9', '1', '4', '6', '8', '2', '0', '4', '6', '2', '7', '9', '5', '4', '3', '1', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_jensenBoundDenominatorChars : List Char := ['7', '8', '5', '1', '2', '5', '0', '4', '5', '5', '9', '8', '4', '9', '7', '1', '7', '5', '3', '9', '1', '7', '5', '7', '8', '6', '7', '4', '1', '6', '8', '0', '5', '3', '4', '5', '3', '4', '7', '6', '2', '3', '2', '6', '0', '7', '3', '4', '6', '0', '1', '9', '4', '7', '8', '2', '7', '2', '8', '0', '2', '4', '2', '6', '8', '3', '7', '7', '8', '1', '8', '8', '6', '2', '2', '8', '2', '9', '0', '9', '3', '2', '5', '0', '8', '7', '0', '1', '8', '7', '6', '3', '3', '7', '4', '7', '0', '0', '0', '2', '5', '6', '3', '7', '8', '0', '9', '9', '8', '7', '7', '2', '1', '0', '2', '2', '0', '5', '9', '8', '1', '1', '5', '7', '4', '9', '6', '0', '0', '1']
noncomputable def geometryRow045_jensenBoundText : String := String.ofList (geometryRow045_jensenBoundNumeratorChars ++ '/' :: geometryRow045_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_jensenBound_before_field"
  err.flush

theorem geometryRow045_jensenBound_field :
    geometryRowsJson045.getObjVal? "jensen_bound" = .ok (.str geometryRow045_jensenBoundText) := by rfl

theorem geometryRow045_jensenBound_numerator_no_slash :
    geometryRow045_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow045_jensenBoundNumeratorChars = some (829740046247140088608936682675453117279850525311533138461015068841564174757914682046279543132812500000000000000000 : Int) := by decide +kernel

theorem geometryRow045_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow045_jensenBoundDenominatorChars = some (7851250455984971753917578674168053453476232607346019478272802426837781886228290932508701876337470002563780998772102205981157496001 : Int) := by decide +kernel

theorem geometryRow045_jensenBound_denominator_nonzero : (7851250455984971753917578674168053453476232607346019478272802426837781886228290932508701876337470002563780998772102205981157496001 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_jensenBound_parse :
    parseRational geometryRow045_jensenBoundText = .ok geometryRowsTyped045.jensenBound :=
  original_rational_fraction_of_chars geometryRow045_jensenBoundNumeratorChars geometryRow045_jensenBoundDenominatorChars
    (829740046247140088608936682675453117279850525311533138461015068841564174757914682046279543132812500000000000000000 : Int) (7851250455984971753917578674168053453476232607346019478272802426837781886228290932508701876337470002563780998772102205981157496001 : Int)
    geometryRow045_jensenBound_numerator_no_slash geometryRow045_jensenBound_numerator_parse
    geometryRow045_jensenBound_denominator_parse geometryRow045_jensenBound_denominator_nonzero

theorem geometryRow045_jensenBound_read :
    rationalField geometryRowsJson045 "jensen_bound" = .ok geometryRowsTyped045.jensenBound :=
  original_rationalField_of_string geometryRowsJson045 "jensen_bound" geometryRow045_jensenBoundText
    geometryRowsTyped045.jensenBound geometryRow045_jensenBound_field geometryRow045_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_factorMaxima_before"
  err.flush

theorem geometryRow045_factorMaxima_read :
    rationalArrayField geometryRowsJson045 "factor_maxima" = .ok geometryRowsTyped045.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_gapWeightedMeans_before"
  err.flush

theorem geometryRow045_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson045 "gap_weighted_means" = .ok geometryRowsTyped045.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow045_floorChars : List Char := ['8', '3', '7', '3', '0', '3', '3', '0', '0', '8', '8', '4', '3']
noncomputable def geometryRow045_floorText : String := String.ofList geometryRow045_floorChars

theorem geometryRow045_floor_text_read :
    geometryRowsJson045.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow045_floorText := by rfl

theorem geometryRow045_floor_chars_parse :
    SourceJson.intChars geometryRow045_floorChars = some (8373033008843 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY00_TYPED Row_045_original_decoder_complete"
  err.flush

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

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
