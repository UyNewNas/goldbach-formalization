import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00500

/-! Original GeometryRow 20: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson020 : SourceJson :=
  (simplicesChunk020Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped020 : GeometryRow :=
  { simplexId := 20,
    vertexIds := #[27, 25, 23, 21, 19, 18, 17, 2, 0],
    physicalVolume := ((12512870500639395095516538733 : ℚ) / (863951454843750000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1640269 : ℚ) / (3744000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((58428763747 : ℚ) / (655200000000 : ℚ)), ((29472724241 : ℚ) / (327600000000 : ℚ)), ((1827118179 : ℚ) / (14560000000 : ℚ)), ((4857817067 : ℚ) / (50400000000 : ℚ)), ((6607391311 : ℚ) / (72800000000 : ℚ)), ((5655657 : ℚ) / (83200000 : ℚ)), ((32119153 : ℚ) / (975000000 : ℚ)), ((93920531 : ℚ) / (2925000000 : ℚ)), ((319502161 : ℚ) / (10237500000 : ℚ)), ((10051688027 : ℚ) / (327600000000 : ℚ))],
    jensenBound := ((389514941244983443192054558606186611999244288000000000000000000000000 : ℚ) / (9306574937021077466882821057069185873558874202152687427058461470106269835630963337951 : ℚ)),
    jensenFloorQ96 := (3315994689295 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_simplexId_before"
  err.flush

theorem geometryRow020_simplexId_read :
    geometryRowsJson020.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped020.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_vertexIds_before"
  err.flush

theorem geometryRow020_vertexIds_read :
    geometryRowsJson020.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped020.vertexIds := by decide +kernel

noncomputable def geometryRow020_physicalVolumeNumeratorChars : List Char := ['1', '2', '5', '1', '2', '8', '7', '0', '5', '0', '0', '6', '3', '9', '3', '9', '5', '0', '9', '5', '5', '1', '6', '5', '3', '8', '7', '3', '3']
noncomputable def geometryRow020_physicalVolumeDenominatorChars : List Char := ['8', '6', '3', '9', '5', '1', '4', '5', '4', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_physicalVolumeText : String := String.ofList (geometryRow020_physicalVolumeNumeratorChars ++ '/' :: geometryRow020_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_physicalVolume_before_field"
  err.flush

theorem geometryRow020_physicalVolume_field :
    geometryRowsJson020.getObjVal? "physical_volume" = .ok (.str geometryRow020_physicalVolumeText) := by rfl

theorem geometryRow020_physicalVolume_numerator_no_slash :
    geometryRow020_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow020_physicalVolumeNumeratorChars = some (12512870500639395095516538733 : Int) := by decide +kernel

theorem geometryRow020_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow020_physicalVolumeDenominatorChars = some (863951454843750000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow020_physicalVolume_denominator_nonzero : (863951454843750000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_physicalVolume_parse :
    parseRational geometryRow020_physicalVolumeText = .ok geometryRowsTyped020.physicalVolume :=
  original_rational_fraction_of_chars geometryRow020_physicalVolumeNumeratorChars geometryRow020_physicalVolumeDenominatorChars
    (12512870500639395095516538733 : Int) (863951454843750000000000000000000000000000000000000000 : Int)
    geometryRow020_physicalVolume_numerator_no_slash geometryRow020_physicalVolume_numerator_parse
    geometryRow020_physicalVolume_denominator_parse geometryRow020_physicalVolume_denominator_nonzero

theorem geometryRow020_physicalVolume_read :
    rationalField geometryRowsJson020 "physical_volume" = .ok geometryRowsTyped020.physicalVolume :=
  original_rationalField_of_string geometryRowsJson020 "physical_volume" geometryRow020_physicalVolumeText
    geometryRowsTyped020.physicalVolume geometryRow020_physicalVolume_field geometryRow020_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_physicalVolume_complete"
  err.flush

noncomputable def geometryRow020_meanGapNumeratorChars : List Char := ['1', '6', '4', '0', '2', '6', '9']
noncomputable def geometryRow020_meanGapDenominatorChars : List Char := ['3', '7', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_meanGapText : String := String.ofList (geometryRow020_meanGapNumeratorChars ++ '/' :: geometryRow020_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_meanGap_before_field"
  err.flush

theorem geometryRow020_meanGap_field :
    geometryRowsJson020.getObjVal? "mean_gap" = .ok (.str geometryRow020_meanGapText) := by rfl

theorem geometryRow020_meanGap_numerator_no_slash :
    geometryRow020_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_meanGap_numerator_parse :
    SourceJson.intChars geometryRow020_meanGapNumeratorChars = some (1640269 : Int) := by decide +kernel

theorem geometryRow020_meanGap_denominator_parse :
    SourceJson.intChars geometryRow020_meanGapDenominatorChars = some (3744000000 : Int) := by decide +kernel

theorem geometryRow020_meanGap_denominator_nonzero : (3744000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_meanGap_parse :
    parseRational geometryRow020_meanGapText = .ok geometryRowsTyped020.meanGap :=
  original_rational_fraction_of_chars geometryRow020_meanGapNumeratorChars geometryRow020_meanGapDenominatorChars
    (1640269 : Int) (3744000000 : Int)
    geometryRow020_meanGap_numerator_no_slash geometryRow020_meanGap_numerator_parse
    geometryRow020_meanGap_denominator_parse geometryRow020_meanGap_denominator_nonzero

theorem geometryRow020_meanGap_read :
    rationalField geometryRowsJson020 "mean_gap" = .ok geometryRowsTyped020.meanGap :=
  original_rationalField_of_string geometryRowsJson020 "mean_gap" geometryRow020_meanGapText
    geometryRowsTyped020.meanGap geometryRow020_meanGap_field geometryRow020_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_meanGap_complete"
  err.flush

noncomputable def geometryRow020_jensenBoundNumeratorChars : List Char := ['3', '8', '9', '5', '1', '4', '9', '4', '1', '2', '4', '4', '9', '8', '3', '4', '4', '3', '1', '9', '2', '0', '5', '4', '5', '5', '8', '6', '0', '6', '1', '8', '6', '6', '1', '1', '9', '9', '9', '2', '4', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_jensenBoundDenominatorChars : List Char := ['9', '3', '0', '6', '5', '7', '4', '9', '3', '7', '0', '2', '1', '0', '7', '7', '4', '6', '6', '8', '8', '2', '8', '2', '1', '0', '5', '7', '0', '6', '9', '1', '8', '5', '8', '7', '3', '5', '5', '8', '8', '7', '4', '2', '0', '2', '1', '5', '2', '6', '8', '7', '4', '2', '7', '0', '5', '8', '4', '6', '1', '4', '7', '0', '1', '0', '6', '2', '6', '9', '8', '3', '5', '6', '3', '0', '9', '6', '3', '3', '3', '7', '9', '5', '1']
noncomputable def geometryRow020_jensenBoundText : String := String.ofList (geometryRow020_jensenBoundNumeratorChars ++ '/' :: geometryRow020_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_jensenBound_before_field"
  err.flush

theorem geometryRow020_jensenBound_field :
    geometryRowsJson020.getObjVal? "jensen_bound" = .ok (.str geometryRow020_jensenBoundText) := by rfl

theorem geometryRow020_jensenBound_numerator_no_slash :
    geometryRow020_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow020_jensenBoundNumeratorChars = some (389514941244983443192054558606186611999244288000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow020_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow020_jensenBoundDenominatorChars = some (9306574937021077466882821057069185873558874202152687427058461470106269835630963337951 : Int) := by decide +kernel

theorem geometryRow020_jensenBound_denominator_nonzero : (9306574937021077466882821057069185873558874202152687427058461470106269835630963337951 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_jensenBound_parse :
    parseRational geometryRow020_jensenBoundText = .ok geometryRowsTyped020.jensenBound :=
  original_rational_fraction_of_chars geometryRow020_jensenBoundNumeratorChars geometryRow020_jensenBoundDenominatorChars
    (389514941244983443192054558606186611999244288000000000000000000000000 : Int) (9306574937021077466882821057069185873558874202152687427058461470106269835630963337951 : Int)
    geometryRow020_jensenBound_numerator_no_slash geometryRow020_jensenBound_numerator_parse
    geometryRow020_jensenBound_denominator_parse geometryRow020_jensenBound_denominator_nonzero

theorem geometryRow020_jensenBound_read :
    rationalField geometryRowsJson020 "jensen_bound" = .ok geometryRowsTyped020.jensenBound :=
  original_rationalField_of_string geometryRowsJson020 "jensen_bound" geometryRow020_jensenBoundText
    geometryRowsTyped020.jensenBound geometryRow020_jensenBound_field geometryRow020_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_factorMaxima_before"
  err.flush

theorem geometryRow020_factorMaxima_read :
    rationalArrayField geometryRowsJson020 "factor_maxima" = .ok geometryRowsTyped020.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_gapWeightedMeans_before"
  err.flush

theorem geometryRow020_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson020 "gap_weighted_means" = .ok geometryRowsTyped020.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow020_floorChars : List Char := ['3', '3', '1', '5', '9', '9', '4', '6', '8', '9', '2', '9', '5']
noncomputable def geometryRow020_floorText : String := String.ofList geometryRow020_floorChars

theorem geometryRow020_floor_text_read :
    geometryRowsJson020.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow020_floorText := by rfl

theorem geometryRow020_floor_chars_parse :
    SourceJson.intChars geometryRow020_floorChars = some (3315994689295 : Int) := by decide +kernel

theorem geometryRow020_floor_parse :
    parseInteger geometryRow020_floorText = .ok geometryRowsTyped020.jensenFloorQ96 := by
  simp only [geometryRow020_floorText, parseInteger, String.toList_ofList, geometryRow020_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_020 :
    decodeGeometryRow geometryRowsJson020 = .ok geometryRowsTyped020 :=
  original_geometryRow_of_fields geometryRowsJson020 geometryRowsTyped020 geometryRow020_floorText
    geometryRow020_simplexId_read geometryRow020_vertexIds_read
    geometryRow020_physicalVolume_read geometryRow020_meanGap_read
    geometryRow020_factorMaxima_read geometryRow020_gapWeightedMeans_read
    geometryRow020_jensenBound_read geometryRow020_floor_text_read geometryRow020_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_020_original_decoder_complete"
  err.flush

#print axioms geometryRow020_simplexId_read
#print axioms geometryRow020_vertexIds_read
#print axioms geometryRow020_physicalVolume_field
#print axioms geometryRow020_physicalVolume_numerator_no_slash
#print axioms geometryRow020_physicalVolume_numerator_parse
#print axioms geometryRow020_physicalVolume_denominator_parse
#print axioms geometryRow020_physicalVolume_denominator_nonzero
#print axioms geometryRow020_physicalVolume_parse
#print axioms geometryRow020_physicalVolume_read
#print axioms geometryRow020_meanGap_field
#print axioms geometryRow020_meanGap_numerator_no_slash
#print axioms geometryRow020_meanGap_numerator_parse
#print axioms geometryRow020_meanGap_denominator_parse
#print axioms geometryRow020_meanGap_denominator_nonzero
#print axioms geometryRow020_meanGap_parse
#print axioms geometryRow020_meanGap_read
#print axioms geometryRow020_jensenBound_field
#print axioms geometryRow020_jensenBound_numerator_no_slash
#print axioms geometryRow020_jensenBound_numerator_parse
#print axioms geometryRow020_jensenBound_denominator_parse
#print axioms geometryRow020_jensenBound_denominator_nonzero
#print axioms geometryRow020_jensenBound_parse
#print axioms geometryRow020_jensenBound_read
#print axioms geometryRow020_factorMaxima_read
#print axioms geometryRow020_gapWeightedMeans_read
#print axioms geometryRow020_floor_text_read
#print axioms geometryRow020_floor_chars_parse
#print axioms geometryRow020_floor_parse
#print axioms decode_geometry_Rows_020

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
