import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01100

/-! Original GeometryRow 46: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson046 : SourceJson :=
  (simplicesChunk046Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped046 : GeometryRow :=
  { simplexId := 46,
    vertexIds := #[27, 15, 11, 9, 8, 6, 5, 3, 1],
    physicalVolume := ((195925354515802640912685068325630219972302573171 : ℚ) / (331728140340559872000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1490621 : ℚ) / (16800000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2209824511773 : ℚ) / (22961120000000 : ℚ)), ((2226342711289 : ℚ) / (22961120000000 : ℚ)), ((123845603746409 : ℚ) / (1033250400000000 : ℚ)), ((45498815080951 : ℚ) / (516625200000000 : ℚ)), ((81626250950011 : ℚ) / (1033250400000000 : ℚ)), ((76132095833431 : ℚ) / (1033250400000000 : ℚ)), ((4752599367961 : ℚ) / (129156300000000 : ℚ)), ((9233594793557 : ℚ) / (258312600000000 : ℚ)), ((35278513908719 : ℚ) / (1033250400000000 : ℚ)), ((3815186449083 : ℚ) / (114805600000000 : ℚ))],
    jensenBound := ((148332138224561621268724508827591379779547931617222514309333473771988678486090625859090620733442000000000000000000000 : ℚ) / (134436650532124224781831503257316080489674982324187662584392288733427653584000916469747381904796822881785600367873853725164616863 : ℚ)),
    jensenFloorQ96 := (87417253456011073 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_simplexId_before"
  err.flush

theorem geometryRow046_simplexId_read :
    geometryRowsJson046.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped046.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_vertexIds_before"
  err.flush

theorem geometryRow046_vertexIds_read :
    geometryRowsJson046.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped046.vertexIds := by decide +kernel

noncomputable def geometryRow046_physicalVolumeNumeratorChars : List Char := ['1', '9', '5', '9', '2', '5', '3', '5', '4', '5', '1', '5', '8', '0', '2', '6', '4', '0', '9', '1', '2', '6', '8', '5', '0', '6', '8', '3', '2', '5', '6', '3', '0', '2', '1', '9', '9', '7', '2', '3', '0', '2', '5', '7', '3', '1', '7', '1']
noncomputable def geometryRow046_physicalVolumeDenominatorChars : List Char := ['3', '3', '1', '7', '2', '8', '1', '4', '0', '3', '4', '0', '5', '5', '9', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_physicalVolumeText : String := String.ofList (geometryRow046_physicalVolumeNumeratorChars ++ '/' :: geometryRow046_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_physicalVolume_before_field"
  err.flush

theorem geometryRow046_physicalVolume_field :
    geometryRowsJson046.getObjVal? "physical_volume" = .ok (.str geometryRow046_physicalVolumeText) := by rfl

theorem geometryRow046_physicalVolume_numerator_no_slash :
    geometryRow046_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow046_physicalVolumeNumeratorChars = some (195925354515802640912685068325630219972302573171 : Int) := by decide +kernel

theorem geometryRow046_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow046_physicalVolumeDenominatorChars = some (331728140340559872000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow046_physicalVolume_denominator_nonzero : (331728140340559872000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_physicalVolume_parse :
    parseRational geometryRow046_physicalVolumeText = .ok geometryRowsTyped046.physicalVolume :=
  original_rational_fraction_of_chars geometryRow046_physicalVolumeNumeratorChars geometryRow046_physicalVolumeDenominatorChars
    (195925354515802640912685068325630219972302573171 : Int) (331728140340559872000000000000000000000000000000000000000000000000000 : Int)
    geometryRow046_physicalVolume_numerator_no_slash geometryRow046_physicalVolume_numerator_parse
    geometryRow046_physicalVolume_denominator_parse geometryRow046_physicalVolume_denominator_nonzero

theorem geometryRow046_physicalVolume_read :
    rationalField geometryRowsJson046 "physical_volume" = .ok geometryRowsTyped046.physicalVolume :=
  original_rationalField_of_string geometryRowsJson046 "physical_volume" geometryRow046_physicalVolumeText
    geometryRowsTyped046.physicalVolume geometryRow046_physicalVolume_field geometryRow046_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_physicalVolume_complete"
  err.flush

noncomputable def geometryRow046_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow046_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_meanGapText : String := String.ofList (geometryRow046_meanGapNumeratorChars ++ '/' :: geometryRow046_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_meanGap_before_field"
  err.flush

theorem geometryRow046_meanGap_field :
    geometryRowsJson046.getObjVal? "mean_gap" = .ok (.str geometryRow046_meanGapText) := by rfl

theorem geometryRow046_meanGap_numerator_no_slash :
    geometryRow046_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_meanGap_numerator_parse :
    SourceJson.intChars geometryRow046_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow046_meanGap_denominator_parse :
    SourceJson.intChars geometryRow046_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow046_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_meanGap_parse :
    parseRational geometryRow046_meanGapText = .ok geometryRowsTyped046.meanGap :=
  original_rational_fraction_of_chars geometryRow046_meanGapNumeratorChars geometryRow046_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow046_meanGap_numerator_no_slash geometryRow046_meanGap_numerator_parse
    geometryRow046_meanGap_denominator_parse geometryRow046_meanGap_denominator_nonzero

theorem geometryRow046_meanGap_read :
    rationalField geometryRowsJson046 "mean_gap" = .ok geometryRowsTyped046.meanGap :=
  original_rationalField_of_string geometryRowsJson046 "mean_gap" geometryRow046_meanGapText
    geometryRowsTyped046.meanGap geometryRow046_meanGap_field geometryRow046_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_meanGap_complete"
  err.flush

noncomputable def geometryRow046_jensenBoundNumeratorChars : List Char := ['1', '4', '8', '3', '3', '2', '1', '3', '8', '2', '2', '4', '5', '6', '1', '6', '2', '1', '2', '6', '8', '7', '2', '4', '5', '0', '8', '8', '2', '7', '5', '9', '1', '3', '7', '9', '7', '7', '9', '5', '4', '7', '9', '3', '1', '6', '1', '7', '2', '2', '2', '5', '1', '4', '3', '0', '9', '3', '3', '3', '4', '7', '3', '7', '7', '1', '9', '8', '8', '6', '7', '8', '4', '8', '6', '0', '9', '0', '6', '2', '5', '8', '5', '9', '0', '9', '0', '6', '2', '0', '7', '3', '3', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_jensenBoundDenominatorChars : List Char := ['1', '3', '4', '4', '3', '6', '6', '5', '0', '5', '3', '2', '1', '2', '4', '2', '2', '4', '7', '8', '1', '8', '3', '1', '5', '0', '3', '2', '5', '7', '3', '1', '6', '0', '8', '0', '4', '8', '9', '6', '7', '4', '9', '8', '2', '3', '2', '4', '1', '8', '7', '6', '6', '2', '5', '8', '4', '3', '9', '2', '2', '8', '8', '7', '3', '3', '4', '2', '7', '6', '5', '3', '5', '8', '4', '0', '0', '0', '9', '1', '6', '4', '6', '9', '7', '4', '7', '3', '8', '1', '9', '0', '4', '7', '9', '6', '8', '2', '2', '8', '8', '1', '7', '8', '5', '6', '0', '0', '3', '6', '7', '8', '7', '3', '8', '5', '3', '7', '2', '5', '1', '6', '4', '6', '1', '6', '8', '6', '3']
noncomputable def geometryRow046_jensenBoundText : String := String.ofList (geometryRow046_jensenBoundNumeratorChars ++ '/' :: geometryRow046_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_jensenBound_before_field"
  err.flush

theorem geometryRow046_jensenBound_field :
    geometryRowsJson046.getObjVal? "jensen_bound" = .ok (.str geometryRow046_jensenBoundText) := by rfl

theorem geometryRow046_jensenBound_numerator_no_slash :
    geometryRow046_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow046_jensenBoundNumeratorChars = some (148332138224561621268724508827591379779547931617222514309333473771988678486090625859090620733442000000000000000000000 : Int) := by decide +kernel

theorem geometryRow046_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow046_jensenBoundDenominatorChars = some (134436650532124224781831503257316080489674982324187662584392288733427653584000916469747381904796822881785600367873853725164616863 : Int) := by decide +kernel

theorem geometryRow046_jensenBound_denominator_nonzero : (134436650532124224781831503257316080489674982324187662584392288733427653584000916469747381904796822881785600367873853725164616863 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_jensenBound_parse :
    parseRational geometryRow046_jensenBoundText = .ok geometryRowsTyped046.jensenBound :=
  original_rational_fraction_of_chars geometryRow046_jensenBoundNumeratorChars geometryRow046_jensenBoundDenominatorChars
    (148332138224561621268724508827591379779547931617222514309333473771988678486090625859090620733442000000000000000000000 : Int) (134436650532124224781831503257316080489674982324187662584392288733427653584000916469747381904796822881785600367873853725164616863 : Int)
    geometryRow046_jensenBound_numerator_no_slash geometryRow046_jensenBound_numerator_parse
    geometryRow046_jensenBound_denominator_parse geometryRow046_jensenBound_denominator_nonzero

theorem geometryRow046_jensenBound_read :
    rationalField geometryRowsJson046 "jensen_bound" = .ok geometryRowsTyped046.jensenBound :=
  original_rationalField_of_string geometryRowsJson046 "jensen_bound" geometryRow046_jensenBoundText
    geometryRowsTyped046.jensenBound geometryRow046_jensenBound_field geometryRow046_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_factorMaxima_before"
  err.flush

theorem geometryRow046_factorMaxima_read :
    rationalArrayField geometryRowsJson046 "factor_maxima" = .ok geometryRowsTyped046.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_gapWeightedMeans_before"
  err.flush

theorem geometryRow046_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson046 "gap_weighted_means" = .ok geometryRowsTyped046.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow046_floorChars : List Char := ['8', '7', '4', '1', '7', '2', '5', '3', '4', '5', '6', '0', '1', '1', '0', '7', '3']
noncomputable def geometryRow046_floorText : String := String.ofList geometryRow046_floorChars

theorem geometryRow046_floor_text_read :
    geometryRowsJson046.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow046_floorText := by rfl

theorem geometryRow046_floor_chars_parse :
    SourceJson.intChars geometryRow046_floorChars = some (87417253456011073 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY00_TYPED Row_046_original_decoder_complete"
  err.flush

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

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
