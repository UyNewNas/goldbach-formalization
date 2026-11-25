import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00800

/-! Original GeometryRow 32: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson032 : SourceJson :=
  (simplicesChunk032Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped032 : GeometryRow :=
  { simplexId := 32,
    vertexIds := #[27, 25, 23, 22, 21, 8, 5, 3, 1],
    physicalVolume := ((1767417077575121881527582131194927 : ℚ) / (91257867540000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((1436760339839 : ℚ) / (15896160000000 : ℚ)), ((1448196016427 : ℚ) / (15896160000000 : ℚ)), ((1092993814469 : ℚ) / (8831200000000 : ℚ)), ((928429712677 : ℚ) / (9935100000000 : ℚ)), ((1386845361803 : ℚ) / (15896160000000 : ℚ)), ((616217293051 : ℚ) / (8831200000000 : ℚ)), ((1380410413723 : ℚ) / (39740400000000 : ℚ)), ((1347301185179 : ℚ) / (39740400000000 : ℚ)), ((504807650489 : ℚ) / (15896160000000 : ℚ)), ((504804471257 : ℚ) / (15896160000000 : ℚ))],
    jensenBound := ((1326065991308697286738316951522601905134970763582277173085368197388388187656893235200000000000000000000 : ℚ) / (29489294114752307804070842852845906738662589456619174280740143956974457425278271419996457726778458654584423011315604993 : ℚ)),
    jensenFloorQ96 := (3562708942954 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_simplexId_before"
  err.flush

theorem geometryRow032_simplexId_read :
    geometryRowsJson032.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped032.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_vertexIds_before"
  err.flush

theorem geometryRow032_vertexIds_read :
    geometryRowsJson032.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped032.vertexIds := by decide +kernel

noncomputable def geometryRow032_physicalVolumeNumeratorChars : List Char := ['1', '7', '6', '7', '4', '1', '7', '0', '7', '7', '5', '7', '5', '1', '2', '1', '8', '8', '1', '5', '2', '7', '5', '8', '2', '1', '3', '1', '1', '9', '4', '9', '2', '7']
noncomputable def geometryRow032_physicalVolumeDenominatorChars : List Char := ['9', '1', '2', '5', '7', '8', '6', '7', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_physicalVolumeText : String := String.ofList (geometryRow032_physicalVolumeNumeratorChars ++ '/' :: geometryRow032_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_physicalVolume_before_field"
  err.flush

theorem geometryRow032_physicalVolume_field :
    geometryRowsJson032.getObjVal? "physical_volume" = .ok (.str geometryRow032_physicalVolumeText) := by rfl

theorem geometryRow032_physicalVolume_numerator_no_slash :
    geometryRow032_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow032_physicalVolumeNumeratorChars = some (1767417077575121881527582131194927 : Int) := by decide +kernel

theorem geometryRow032_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow032_physicalVolumeDenominatorChars = some (91257867540000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow032_physicalVolume_denominator_nonzero : (91257867540000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_physicalVolume_parse :
    parseRational geometryRow032_physicalVolumeText = .ok geometryRowsTyped032.physicalVolume :=
  original_rational_fraction_of_chars geometryRow032_physicalVolumeNumeratorChars geometryRow032_physicalVolumeDenominatorChars
    (1767417077575121881527582131194927 : Int) (91257867540000000000000000000000000000000000000000000000000 : Int)
    geometryRow032_physicalVolume_numerator_no_slash geometryRow032_physicalVolume_numerator_parse
    geometryRow032_physicalVolume_denominator_parse geometryRow032_physicalVolume_denominator_nonzero

theorem geometryRow032_physicalVolume_read :
    rationalField geometryRowsJson032 "physical_volume" = .ok geometryRowsTyped032.physicalVolume :=
  original_rationalField_of_string geometryRowsJson032 "physical_volume" geometryRow032_physicalVolumeText
    geometryRowsTyped032.physicalVolume geometryRow032_physicalVolume_field geometryRow032_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_physicalVolume_complete"
  err.flush

noncomputable def geometryRow032_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow032_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_meanGapText : String := String.ofList (geometryRow032_meanGapNumeratorChars ++ '/' :: geometryRow032_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_meanGap_before_field"
  err.flush

theorem geometryRow032_meanGap_field :
    geometryRowsJson032.getObjVal? "mean_gap" = .ok (.str geometryRow032_meanGapText) := by rfl

theorem geometryRow032_meanGap_numerator_no_slash :
    geometryRow032_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_meanGap_numerator_parse :
    SourceJson.intChars geometryRow032_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow032_meanGap_denominator_parse :
    SourceJson.intChars geometryRow032_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow032_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_meanGap_parse :
    parseRational geometryRow032_meanGapText = .ok geometryRowsTyped032.meanGap :=
  original_rational_fraction_of_chars geometryRow032_meanGapNumeratorChars geometryRow032_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow032_meanGap_numerator_no_slash geometryRow032_meanGap_numerator_parse
    geometryRow032_meanGap_denominator_parse geometryRow032_meanGap_denominator_nonzero

theorem geometryRow032_meanGap_read :
    rationalField geometryRowsJson032 "mean_gap" = .ok geometryRowsTyped032.meanGap :=
  original_rationalField_of_string geometryRowsJson032 "mean_gap" geometryRow032_meanGapText
    geometryRowsTyped032.meanGap geometryRow032_meanGap_field geometryRow032_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_meanGap_complete"
  err.flush

noncomputable def geometryRow032_jensenBoundNumeratorChars : List Char := ['1', '3', '2', '6', '0', '6', '5', '9', '9', '1', '3', '0', '8', '6', '9', '7', '2', '8', '6', '7', '3', '8', '3', '1', '6', '9', '5', '1', '5', '2', '2', '6', '0', '1', '9', '0', '5', '1', '3', '4', '9', '7', '0', '7', '6', '3', '5', '8', '2', '2', '7', '7', '1', '7', '3', '0', '8', '5', '3', '6', '8', '1', '9', '7', '3', '8', '8', '3', '8', '8', '1', '8', '7', '6', '5', '6', '8', '9', '3', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_jensenBoundDenominatorChars : List Char := ['2', '9', '4', '8', '9', '2', '9', '4', '1', '1', '4', '7', '5', '2', '3', '0', '7', '8', '0', '4', '0', '7', '0', '8', '4', '2', '8', '5', '2', '8', '4', '5', '9', '0', '6', '7', '3', '8', '6', '6', '2', '5', '8', '9', '4', '5', '6', '6', '1', '9', '1', '7', '4', '2', '8', '0', '7', '4', '0', '1', '4', '3', '9', '5', '6', '9', '7', '4', '4', '5', '7', '4', '2', '5', '2', '7', '8', '2', '7', '1', '4', '1', '9', '9', '9', '6', '4', '5', '7', '7', '2', '6', '7', '7', '8', '4', '5', '8', '6', '5', '4', '5', '8', '4', '4', '2', '3', '0', '1', '1', '3', '1', '5', '6', '0', '4', '9', '9', '3']
noncomputable def geometryRow032_jensenBoundText : String := String.ofList (geometryRow032_jensenBoundNumeratorChars ++ '/' :: geometryRow032_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_jensenBound_before_field"
  err.flush

theorem geometryRow032_jensenBound_field :
    geometryRowsJson032.getObjVal? "jensen_bound" = .ok (.str geometryRow032_jensenBoundText) := by rfl

theorem geometryRow032_jensenBound_numerator_no_slash :
    geometryRow032_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow032_jensenBoundNumeratorChars = some (1326065991308697286738316951522601905134970763582277173085368197388388187656893235200000000000000000000 : Int) := by decide +kernel

theorem geometryRow032_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow032_jensenBoundDenominatorChars = some (29489294114752307804070842852845906738662589456619174280740143956974457425278271419996457726778458654584423011315604993 : Int) := by decide +kernel

theorem geometryRow032_jensenBound_denominator_nonzero : (29489294114752307804070842852845906738662589456619174280740143956974457425278271419996457726778458654584423011315604993 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_jensenBound_parse :
    parseRational geometryRow032_jensenBoundText = .ok geometryRowsTyped032.jensenBound :=
  original_rational_fraction_of_chars geometryRow032_jensenBoundNumeratorChars geometryRow032_jensenBoundDenominatorChars
    (1326065991308697286738316951522601905134970763582277173085368197388388187656893235200000000000000000000 : Int) (29489294114752307804070842852845906738662589456619174280740143956974457425278271419996457726778458654584423011315604993 : Int)
    geometryRow032_jensenBound_numerator_no_slash geometryRow032_jensenBound_numerator_parse
    geometryRow032_jensenBound_denominator_parse geometryRow032_jensenBound_denominator_nonzero

theorem geometryRow032_jensenBound_read :
    rationalField geometryRowsJson032 "jensen_bound" = .ok geometryRowsTyped032.jensenBound :=
  original_rationalField_of_string geometryRowsJson032 "jensen_bound" geometryRow032_jensenBoundText
    geometryRowsTyped032.jensenBound geometryRow032_jensenBound_field geometryRow032_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_factorMaxima_before"
  err.flush

theorem geometryRow032_factorMaxima_read :
    rationalArrayField geometryRowsJson032 "factor_maxima" = .ok geometryRowsTyped032.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_gapWeightedMeans_before"
  err.flush

theorem geometryRow032_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson032 "gap_weighted_means" = .ok geometryRowsTyped032.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow032_floorChars : List Char := ['3', '5', '6', '2', '7', '0', '8', '9', '4', '2', '9', '5', '4']
noncomputable def geometryRow032_floorText : String := String.ofList geometryRow032_floorChars

theorem geometryRow032_floor_text_read :
    geometryRowsJson032.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow032_floorText := by rfl

theorem geometryRow032_floor_chars_parse :
    SourceJson.intChars geometryRow032_floorChars = some (3562708942954 : Int) := by decide +kernel

theorem geometryRow032_floor_parse :
    parseInteger geometryRow032_floorText = .ok geometryRowsTyped032.jensenFloorQ96 := by
  simp only [geometryRow032_floorText, parseInteger, String.toList_ofList, geometryRow032_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_032 :
    decodeGeometryRow geometryRowsJson032 = .ok geometryRowsTyped032 :=
  original_geometryRow_of_fields geometryRowsJson032 geometryRowsTyped032 geometryRow032_floorText
    geometryRow032_simplexId_read geometryRow032_vertexIds_read
    geometryRow032_physicalVolume_read geometryRow032_meanGap_read
    geometryRow032_factorMaxima_read geometryRow032_gapWeightedMeans_read
    geometryRow032_jensenBound_read geometryRow032_floor_text_read geometryRow032_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_032_original_decoder_complete"
  err.flush

#print axioms geometryRow032_simplexId_read
#print axioms geometryRow032_vertexIds_read
#print axioms geometryRow032_physicalVolume_field
#print axioms geometryRow032_physicalVolume_numerator_no_slash
#print axioms geometryRow032_physicalVolume_numerator_parse
#print axioms geometryRow032_physicalVolume_denominator_parse
#print axioms geometryRow032_physicalVolume_denominator_nonzero
#print axioms geometryRow032_physicalVolume_parse
#print axioms geometryRow032_physicalVolume_read
#print axioms geometryRow032_meanGap_field
#print axioms geometryRow032_meanGap_numerator_no_slash
#print axioms geometryRow032_meanGap_numerator_parse
#print axioms geometryRow032_meanGap_denominator_parse
#print axioms geometryRow032_meanGap_denominator_nonzero
#print axioms geometryRow032_meanGap_parse
#print axioms geometryRow032_meanGap_read
#print axioms geometryRow032_jensenBound_field
#print axioms geometryRow032_jensenBound_numerator_no_slash
#print axioms geometryRow032_jensenBound_numerator_parse
#print axioms geometryRow032_jensenBound_denominator_parse
#print axioms geometryRow032_jensenBound_denominator_nonzero
#print axioms geometryRow032_jensenBound_parse
#print axioms geometryRow032_jensenBound_read
#print axioms geometryRow032_factorMaxima_read
#print axioms geometryRow032_gapWeightedMeans_read
#print axioms geometryRow032_floor_text_read
#print axioms geometryRow032_floor_chars_parse
#print axioms geometryRow032_floor_parse
#print axioms decode_geometry_Rows_032

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
