import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00400

/-! Original GeometryRow 18: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson018 : SourceJson :=
  (simplicesChunk018Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped018 : GeometryRow :=
  { simplexId := 18,
    vertexIds := #[27, 25, 23, 21, 19, 18, 3, 1, 0],
    physicalVolume := ((365865662483184032789876371 : ℚ) / (27690751757812500000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((5449755841 : ℚ) / (59850000000 : ℚ)), ((21971247409 : ℚ) / (239400000000 : ℚ)), ((3966569977 : ℚ) / (31920000000 : ℚ)), ((45208483189 : ℚ) / (478800000000 : ℚ)), ((14201290007 : ℚ) / (159600000000 : ℚ)), ((2213267051 : ℚ) / (31920000000 : ℚ)), ((2673313379 : ℚ) / (79800000000 : ℚ)), ((7820486953 : ℚ) / (239400000000 : ℚ)), ((7490023963 : ℚ) / (239400000000 : ℚ)), ((7489960123 : ℚ) / (239400000000 : ℚ))],
    jensenBound := ((30677817492663653625609614216549981073218130157051576320000000000000000000000000 : ℚ) / (941193276449973847632913748287351087910620371229199638183867394943504902921942490901920504679907 : ℚ)),
    jensenFloorQ96 := (2582410192154 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_simplexId_before"
  err.flush

theorem geometryRow018_simplexId_read :
    geometryRowsJson018.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped018.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_vertexIds_before"
  err.flush

theorem geometryRow018_vertexIds_read :
    geometryRowsJson018.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped018.vertexIds := by decide +kernel

noncomputable def geometryRow018_physicalVolumeNumeratorChars : List Char := ['3', '6', '5', '8', '6', '5', '6', '6', '2', '4', '8', '3', '1', '8', '4', '0', '3', '2', '7', '8', '9', '8', '7', '6', '3', '7', '1']
noncomputable def geometryRow018_physicalVolumeDenominatorChars : List Char := ['2', '7', '6', '9', '0', '7', '5', '1', '7', '5', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_physicalVolumeText : String := String.ofList (geometryRow018_physicalVolumeNumeratorChars ++ '/' :: geometryRow018_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_physicalVolume_before_field"
  err.flush

theorem geometryRow018_physicalVolume_field :
    geometryRowsJson018.getObjVal? "physical_volume" = .ok (.str geometryRow018_physicalVolumeText) := by rfl

theorem geometryRow018_physicalVolume_numerator_no_slash :
    geometryRow018_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow018_physicalVolumeNumeratorChars = some (365865662483184032789876371 : Int) := by decide +kernel

theorem geometryRow018_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow018_physicalVolumeDenominatorChars = some (27690751757812500000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow018_physicalVolume_denominator_nonzero : (27690751757812500000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_physicalVolume_parse :
    parseRational geometryRow018_physicalVolumeText = .ok geometryRowsTyped018.physicalVolume :=
  original_rational_fraction_of_chars geometryRow018_physicalVolumeNumeratorChars geometryRow018_physicalVolumeDenominatorChars
    (365865662483184032789876371 : Int) (27690751757812500000000000000000000000000000000000000 : Int)
    geometryRow018_physicalVolume_numerator_no_slash geometryRow018_physicalVolume_numerator_parse
    geometryRow018_physicalVolume_denominator_parse geometryRow018_physicalVolume_denominator_nonzero

theorem geometryRow018_physicalVolume_read :
    rationalField geometryRowsJson018 "physical_volume" = .ok geometryRowsTyped018.physicalVolume :=
  original_rationalField_of_string geometryRowsJson018 "physical_volume" geometryRow018_physicalVolumeText
    geometryRowsTyped018.physicalVolume geometryRow018_physicalVolume_field geometryRow018_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_physicalVolume_complete"
  err.flush

noncomputable def geometryRow018_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow018_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_meanGapText : String := String.ofList (geometryRow018_meanGapNumeratorChars ++ '/' :: geometryRow018_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_meanGap_before_field"
  err.flush

theorem geometryRow018_meanGap_field :
    geometryRowsJson018.getObjVal? "mean_gap" = .ok (.str geometryRow018_meanGapText) := by rfl

theorem geometryRow018_meanGap_numerator_no_slash :
    geometryRow018_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_meanGap_numerator_parse :
    SourceJson.intChars geometryRow018_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow018_meanGap_denominator_parse :
    SourceJson.intChars geometryRow018_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow018_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_meanGap_parse :
    parseRational geometryRow018_meanGapText = .ok geometryRowsTyped018.meanGap :=
  original_rational_fraction_of_chars geometryRow018_meanGapNumeratorChars geometryRow018_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow018_meanGap_numerator_no_slash geometryRow018_meanGap_numerator_parse
    geometryRow018_meanGap_denominator_parse geometryRow018_meanGap_denominator_nonzero

theorem geometryRow018_meanGap_read :
    rationalField geometryRowsJson018 "mean_gap" = .ok geometryRowsTyped018.meanGap :=
  original_rationalField_of_string geometryRowsJson018 "mean_gap" geometryRow018_meanGapText
    geometryRowsTyped018.meanGap geometryRow018_meanGap_field geometryRow018_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_meanGap_complete"
  err.flush

noncomputable def geometryRow018_jensenBoundNumeratorChars : List Char := ['3', '0', '6', '7', '7', '8', '1', '7', '4', '9', '2', '6', '6', '3', '6', '5', '3', '6', '2', '5', '6', '0', '9', '6', '1', '4', '2', '1', '6', '5', '4', '9', '9', '8', '1', '0', '7', '3', '2', '1', '8', '1', '3', '0', '1', '5', '7', '0', '5', '1', '5', '7', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_jensenBoundDenominatorChars : List Char := ['9', '4', '1', '1', '9', '3', '2', '7', '6', '4', '4', '9', '9', '7', '3', '8', '4', '7', '6', '3', '2', '9', '1', '3', '7', '4', '8', '2', '8', '7', '3', '5', '1', '0', '8', '7', '9', '1', '0', '6', '2', '0', '3', '7', '1', '2', '2', '9', '1', '9', '9', '6', '3', '8', '1', '8', '3', '8', '6', '7', '3', '9', '4', '9', '4', '3', '5', '0', '4', '9', '0', '2', '9', '2', '1', '9', '4', '2', '4', '9', '0', '9', '0', '1', '9', '2', '0', '5', '0', '4', '6', '7', '9', '9', '0', '7']
noncomputable def geometryRow018_jensenBoundText : String := String.ofList (geometryRow018_jensenBoundNumeratorChars ++ '/' :: geometryRow018_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_jensenBound_before_field"
  err.flush

theorem geometryRow018_jensenBound_field :
    geometryRowsJson018.getObjVal? "jensen_bound" = .ok (.str geometryRow018_jensenBoundText) := by rfl

theorem geometryRow018_jensenBound_numerator_no_slash :
    geometryRow018_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow018_jensenBoundNumeratorChars = some (30677817492663653625609614216549981073218130157051576320000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow018_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow018_jensenBoundDenominatorChars = some (941193276449973847632913748287351087910620371229199638183867394943504902921942490901920504679907 : Int) := by decide +kernel

theorem geometryRow018_jensenBound_denominator_nonzero : (941193276449973847632913748287351087910620371229199638183867394943504902921942490901920504679907 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_jensenBound_parse :
    parseRational geometryRow018_jensenBoundText = .ok geometryRowsTyped018.jensenBound :=
  original_rational_fraction_of_chars geometryRow018_jensenBoundNumeratorChars geometryRow018_jensenBoundDenominatorChars
    (30677817492663653625609614216549981073218130157051576320000000000000000000000000 : Int) (941193276449973847632913748287351087910620371229199638183867394943504902921942490901920504679907 : Int)
    geometryRow018_jensenBound_numerator_no_slash geometryRow018_jensenBound_numerator_parse
    geometryRow018_jensenBound_denominator_parse geometryRow018_jensenBound_denominator_nonzero

theorem geometryRow018_jensenBound_read :
    rationalField geometryRowsJson018 "jensen_bound" = .ok geometryRowsTyped018.jensenBound :=
  original_rationalField_of_string geometryRowsJson018 "jensen_bound" geometryRow018_jensenBoundText
    geometryRowsTyped018.jensenBound geometryRow018_jensenBound_field geometryRow018_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_factorMaxima_before"
  err.flush

theorem geometryRow018_factorMaxima_read :
    rationalArrayField geometryRowsJson018 "factor_maxima" = .ok geometryRowsTyped018.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_gapWeightedMeans_before"
  err.flush

theorem geometryRow018_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson018 "gap_weighted_means" = .ok geometryRowsTyped018.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow018_floorChars : List Char := ['2', '5', '8', '2', '4', '1', '0', '1', '9', '2', '1', '5', '4']
noncomputable def geometryRow018_floorText : String := String.ofList geometryRow018_floorChars

theorem geometryRow018_floor_text_read :
    geometryRowsJson018.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow018_floorText := by rfl

theorem geometryRow018_floor_chars_parse :
    SourceJson.intChars geometryRow018_floorChars = some (2582410192154 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY00_TYPED Row_018_original_decoder_complete"
  err.flush

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

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
