import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01100

/-! Original GeometryRow 44: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson044 : SourceJson :=
  (simplicesChunk044Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped044 : GeometryRow :=
  { simplexId := 44,
    vertexIds := #[27, 15, 11, 9, 7, 5, 4, 2, 0],
    physicalVolume := ((377913403796871620900581787810346378957830237221 : ℚ) / (762382351104108134400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1640269 : ℚ) / (3744000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1490621 : ℚ) / (16800000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((120946631193951 : ℚ) / (1262861600000000 : ℚ)), ((30485628078989 : ℚ) / (315715400000000 : ℚ)), ((453966462348967 : ℚ) / (3788584800000000 : ℚ)), ((1003663278135071 : ℚ) / (11365754400000000 : ℚ)), ((100033552190701 : ℚ) / (1262861600000000 : ℚ)), ((277274147674523 : ℚ) / (3788584800000000 : ℚ)), ((207706640475391 : ℚ) / (5682877200000000 : ℚ)), ((15517796441797 : ℚ) / (437144400000000 : ℚ)), ((15325794896677 : ℚ) / (437144400000000 : ℚ)), ((4702308757709 : ℚ) / (142071930000000 : ℚ))],
    jensenBound := ((2540519643223059382314524513767655594374823562551847569086706834516808960670636295182713532141325930698525000000000000000000000 : ℚ) / (2497746060415315574933949226974471784643861717805452651244941502380040100375392267141709448166087840098715677029596278009721627718718251689 : ℚ)),
    jensenFloorQ96 := (80584934695278519 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_simplexId_before"
  err.flush

theorem geometryRow044_simplexId_read :
    geometryRowsJson044.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped044.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_vertexIds_before"
  err.flush

theorem geometryRow044_vertexIds_read :
    geometryRowsJson044.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped044.vertexIds := by decide +kernel

noncomputable def geometryRow044_physicalVolumeNumeratorChars : List Char := ['3', '7', '7', '9', '1', '3', '4', '0', '3', '7', '9', '6', '8', '7', '1', '6', '2', '0', '9', '0', '0', '5', '8', '1', '7', '8', '7', '8', '1', '0', '3', '4', '6', '3', '7', '8', '9', '5', '7', '8', '3', '0', '2', '3', '7', '2', '2', '1']
noncomputable def geometryRow044_physicalVolumeDenominatorChars : List Char := ['7', '6', '2', '3', '8', '2', '3', '5', '1', '1', '0', '4', '1', '0', '8', '1', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_physicalVolumeText : String := String.ofList (geometryRow044_physicalVolumeNumeratorChars ++ '/' :: geometryRow044_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_physicalVolume_before_field"
  err.flush

theorem geometryRow044_physicalVolume_field :
    geometryRowsJson044.getObjVal? "physical_volume" = .ok (.str geometryRow044_physicalVolumeText) := by rfl

theorem geometryRow044_physicalVolume_numerator_no_slash :
    geometryRow044_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow044_physicalVolumeNumeratorChars = some (377913403796871620900581787810346378957830237221 : Int) := by decide +kernel

theorem geometryRow044_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow044_physicalVolumeDenominatorChars = some (762382351104108134400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow044_physicalVolume_denominator_nonzero : (762382351104108134400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_physicalVolume_parse :
    parseRational geometryRow044_physicalVolumeText = .ok geometryRowsTyped044.physicalVolume :=
  original_rational_fraction_of_chars geometryRow044_physicalVolumeNumeratorChars geometryRow044_physicalVolumeDenominatorChars
    (377913403796871620900581787810346378957830237221 : Int) (762382351104108134400000000000000000000000000000000000000000000000000 : Int)
    geometryRow044_physicalVolume_numerator_no_slash geometryRow044_physicalVolume_numerator_parse
    geometryRow044_physicalVolume_denominator_parse geometryRow044_physicalVolume_denominator_nonzero

theorem geometryRow044_physicalVolume_read :
    rationalField geometryRowsJson044 "physical_volume" = .ok geometryRowsTyped044.physicalVolume :=
  original_rationalField_of_string geometryRowsJson044 "physical_volume" geometryRow044_physicalVolumeText
    geometryRowsTyped044.physicalVolume geometryRow044_physicalVolume_field geometryRow044_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_physicalVolume_complete"
  err.flush

noncomputable def geometryRow044_meanGapNumeratorChars : List Char := ['1', '6', '4', '0', '2', '6', '9']
noncomputable def geometryRow044_meanGapDenominatorChars : List Char := ['3', '7', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_meanGapText : String := String.ofList (geometryRow044_meanGapNumeratorChars ++ '/' :: geometryRow044_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_meanGap_before_field"
  err.flush

theorem geometryRow044_meanGap_field :
    geometryRowsJson044.getObjVal? "mean_gap" = .ok (.str geometryRow044_meanGapText) := by rfl

theorem geometryRow044_meanGap_numerator_no_slash :
    geometryRow044_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_meanGap_numerator_parse :
    SourceJson.intChars geometryRow044_meanGapNumeratorChars = some (1640269 : Int) := by decide +kernel

theorem geometryRow044_meanGap_denominator_parse :
    SourceJson.intChars geometryRow044_meanGapDenominatorChars = some (3744000000 : Int) := by decide +kernel

theorem geometryRow044_meanGap_denominator_nonzero : (3744000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_meanGap_parse :
    parseRational geometryRow044_meanGapText = .ok geometryRowsTyped044.meanGap :=
  original_rational_fraction_of_chars geometryRow044_meanGapNumeratorChars geometryRow044_meanGapDenominatorChars
    (1640269 : Int) (3744000000 : Int)
    geometryRow044_meanGap_numerator_no_slash geometryRow044_meanGap_numerator_parse
    geometryRow044_meanGap_denominator_parse geometryRow044_meanGap_denominator_nonzero

theorem geometryRow044_meanGap_read :
    rationalField geometryRowsJson044 "mean_gap" = .ok geometryRowsTyped044.meanGap :=
  original_rationalField_of_string geometryRowsJson044 "mean_gap" geometryRow044_meanGapText
    geometryRowsTyped044.meanGap geometryRow044_meanGap_field geometryRow044_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_meanGap_complete"
  err.flush

noncomputable def geometryRow044_jensenBoundNumeratorChars : List Char := ['2', '5', '4', '0', '5', '1', '9', '6', '4', '3', '2', '2', '3', '0', '5', '9', '3', '8', '2', '3', '1', '4', '5', '2', '4', '5', '1', '3', '7', '6', '7', '6', '5', '5', '5', '9', '4', '3', '7', '4', '8', '2', '3', '5', '6', '2', '5', '5', '1', '8', '4', '7', '5', '6', '9', '0', '8', '6', '7', '0', '6', '8', '3', '4', '5', '1', '6', '8', '0', '8', '9', '6', '0', '6', '7', '0', '6', '3', '6', '2', '9', '5', '1', '8', '2', '7', '1', '3', '5', '3', '2', '1', '4', '1', '3', '2', '5', '9', '3', '0', '6', '9', '8', '5', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_jensenBoundDenominatorChars : List Char := ['2', '4', '9', '7', '7', '4', '6', '0', '6', '0', '4', '1', '5', '3', '1', '5', '5', '7', '4', '9', '3', '3', '9', '4', '9', '2', '2', '6', '9', '7', '4', '4', '7', '1', '7', '8', '4', '6', '4', '3', '8', '6', '1', '7', '1', '7', '8', '0', '5', '4', '5', '2', '6', '5', '1', '2', '4', '4', '9', '4', '1', '5', '0', '2', '3', '8', '0', '0', '4', '0', '1', '0', '0', '3', '7', '5', '3', '9', '2', '2', '6', '7', '1', '4', '1', '7', '0', '9', '4', '4', '8', '1', '6', '6', '0', '8', '7', '8', '4', '0', '0', '9', '8', '7', '1', '5', '6', '7', '7', '0', '2', '9', '5', '9', '6', '2', '7', '8', '0', '0', '9', '7', '2', '1', '6', '2', '7', '7', '1', '8', '7', '1', '8', '2', '5', '1', '6', '8', '9']
noncomputable def geometryRow044_jensenBoundText : String := String.ofList (geometryRow044_jensenBoundNumeratorChars ++ '/' :: geometryRow044_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_jensenBound_before_field"
  err.flush

theorem geometryRow044_jensenBound_field :
    geometryRowsJson044.getObjVal? "jensen_bound" = .ok (.str geometryRow044_jensenBoundText) := by rfl

theorem geometryRow044_jensenBound_numerator_no_slash :
    geometryRow044_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow044_jensenBoundNumeratorChars = some (2540519643223059382314524513767655594374823562551847569086706834516808960670636295182713532141325930698525000000000000000000000 : Int) := by decide +kernel

theorem geometryRow044_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow044_jensenBoundDenominatorChars = some (2497746060415315574933949226974471784643861717805452651244941502380040100375392267141709448166087840098715677029596278009721627718718251689 : Int) := by decide +kernel

theorem geometryRow044_jensenBound_denominator_nonzero : (2497746060415315574933949226974471784643861717805452651244941502380040100375392267141709448166087840098715677029596278009721627718718251689 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_jensenBound_parse :
    parseRational geometryRow044_jensenBoundText = .ok geometryRowsTyped044.jensenBound :=
  original_rational_fraction_of_chars geometryRow044_jensenBoundNumeratorChars geometryRow044_jensenBoundDenominatorChars
    (2540519643223059382314524513767655594374823562551847569086706834516808960670636295182713532141325930698525000000000000000000000 : Int) (2497746060415315574933949226974471784643861717805452651244941502380040100375392267141709448166087840098715677029596278009721627718718251689 : Int)
    geometryRow044_jensenBound_numerator_no_slash geometryRow044_jensenBound_numerator_parse
    geometryRow044_jensenBound_denominator_parse geometryRow044_jensenBound_denominator_nonzero

theorem geometryRow044_jensenBound_read :
    rationalField geometryRowsJson044 "jensen_bound" = .ok geometryRowsTyped044.jensenBound :=
  original_rationalField_of_string geometryRowsJson044 "jensen_bound" geometryRow044_jensenBoundText
    geometryRowsTyped044.jensenBound geometryRow044_jensenBound_field geometryRow044_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_factorMaxima_before"
  err.flush

theorem geometryRow044_factorMaxima_read :
    rationalArrayField geometryRowsJson044 "factor_maxima" = .ok geometryRowsTyped044.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_gapWeightedMeans_before"
  err.flush

theorem geometryRow044_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson044 "gap_weighted_means" = .ok geometryRowsTyped044.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow044_floorChars : List Char := ['8', '0', '5', '8', '4', '9', '3', '4', '6', '9', '5', '2', '7', '8', '5', '1', '9']
noncomputable def geometryRow044_floorText : String := String.ofList geometryRow044_floorChars

theorem geometryRow044_floor_text_read :
    geometryRowsJson044.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow044_floorText := by rfl

theorem geometryRow044_floor_chars_parse :
    SourceJson.intChars geometryRow044_floorChars = some (80584934695278519 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY00_TYPED Row_044_original_decoder_complete"
  err.flush

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

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
