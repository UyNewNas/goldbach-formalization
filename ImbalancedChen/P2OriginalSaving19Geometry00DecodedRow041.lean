import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01000

/-! Original GeometryRow 41: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson041 : SourceJson :=
  (simplicesChunk041Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped041 : GeometryRow :=
  { simplexId := 41,
    vertexIds := #[27, 25, 24, 22, 21, 19, 18, 13, 3],
    physicalVolume := ((355127352385777798434180599 : ℚ) / (63572649411600000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((20250079 : ℚ) / (26904000000 : ℚ)),
    factorMaxima := #[((14640661 : ℚ) / (152000000 : ℚ)), ((3796851 : ℚ) / (38000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((8140597 : ℚ) / (114000000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((1265617 : ℚ) / (38000000 : ℚ)), ((1265617 : ℚ) / (38000000 : ℚ))],
    gapWeightedMeans := #[((25013802296943841589 : ℚ) / (286024265843400000000 : ℚ)), ((12652404273754332667 : ℚ) / (143012132921700000000 : ℚ)), ((3630256468119839707 : ℚ) / (28602426584340000000 : ℚ)), ((14125819026711115291 : ℚ) / (143012132921700000000 : ℚ)), ((13115051239021453879 : ℚ) / (143012132921700000000 : ℚ)), ((472559299483685231 : ℚ) / (7150606646085000000 : ℚ)), ((298807013855174401 : ℚ) / (8938258307606250000 : ℚ)), ((63091922418116357 : ℚ) / (1986279623912500000 : ℚ)), ((4316774657003139949 : ℚ) / (143012132921700000000 : ℚ)), ((4316755588718750389 : ℚ) / (143012132921700000000 : ℚ))],
    jensenBound := ((25903884721724217043748258513844841166782625869347360361958444381528441553641371347930694792884232639571413702787502878452242574089401894531250000000000000000000000 : ℚ) / (875964050528673756539851555580054266419718558585618717008240745526435214762771196499657630017019971864219583097086599660014702106477763522462530918087561424745076973500393297974017 : ℚ)),
    jensenFloorQ96 := (2342923990139 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_simplexId_before"
  err.flush

theorem geometryRow041_simplexId_read :
    geometryRowsJson041.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped041.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_vertexIds_before"
  err.flush

theorem geometryRow041_vertexIds_read :
    geometryRowsJson041.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped041.vertexIds := by decide +kernel

noncomputable def geometryRow041_physicalVolumeNumeratorChars : List Char := ['3', '5', '5', '1', '2', '7', '3', '5', '2', '3', '8', '5', '7', '7', '7', '7', '9', '8', '4', '3', '4', '1', '8', '0', '5', '9', '9']
noncomputable def geometryRow041_physicalVolumeDenominatorChars : List Char := ['6', '3', '5', '7', '2', '6', '4', '9', '4', '1', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_physicalVolumeText : String := String.ofList (geometryRow041_physicalVolumeNumeratorChars ++ '/' :: geometryRow041_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_physicalVolume_before_field"
  err.flush

theorem geometryRow041_physicalVolume_field :
    geometryRowsJson041.getObjVal? "physical_volume" = .ok (.str geometryRow041_physicalVolumeText) := by rfl

theorem geometryRow041_physicalVolume_numerator_no_slash :
    geometryRow041_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow041_physicalVolumeNumeratorChars = some (355127352385777798434180599 : Int) := by decide +kernel

theorem geometryRow041_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow041_physicalVolumeDenominatorChars = some (63572649411600000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow041_physicalVolume_denominator_nonzero : (63572649411600000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_physicalVolume_parse :
    parseRational geometryRow041_physicalVolumeText = .ok geometryRowsTyped041.physicalVolume :=
  original_rational_fraction_of_chars geometryRow041_physicalVolumeNumeratorChars geometryRow041_physicalVolumeDenominatorChars
    (355127352385777798434180599 : Int) (63572649411600000000000000000000000000000000000000000 : Int)
    geometryRow041_physicalVolume_numerator_no_slash geometryRow041_physicalVolume_numerator_parse
    geometryRow041_physicalVolume_denominator_parse geometryRow041_physicalVolume_denominator_nonzero

theorem geometryRow041_physicalVolume_read :
    rationalField geometryRowsJson041 "physical_volume" = .ok geometryRowsTyped041.physicalVolume :=
  original_rationalField_of_string geometryRowsJson041 "physical_volume" geometryRow041_physicalVolumeText
    geometryRowsTyped041.physicalVolume geometryRow041_physicalVolume_field geometryRow041_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_physicalVolume_complete"
  err.flush

noncomputable def geometryRow041_meanGapNumeratorChars : List Char := ['2', '0', '2', '5', '0', '0', '7', '9']
noncomputable def geometryRow041_meanGapDenominatorChars : List Char := ['2', '6', '9', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_meanGapText : String := String.ofList (geometryRow041_meanGapNumeratorChars ++ '/' :: geometryRow041_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_meanGap_before_field"
  err.flush

theorem geometryRow041_meanGap_field :
    geometryRowsJson041.getObjVal? "mean_gap" = .ok (.str geometryRow041_meanGapText) := by rfl

theorem geometryRow041_meanGap_numerator_no_slash :
    geometryRow041_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_meanGap_numerator_parse :
    SourceJson.intChars geometryRow041_meanGapNumeratorChars = some (20250079 : Int) := by decide +kernel

theorem geometryRow041_meanGap_denominator_parse :
    SourceJson.intChars geometryRow041_meanGapDenominatorChars = some (26904000000 : Int) := by decide +kernel

theorem geometryRow041_meanGap_denominator_nonzero : (26904000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_meanGap_parse :
    parseRational geometryRow041_meanGapText = .ok geometryRowsTyped041.meanGap :=
  original_rational_fraction_of_chars geometryRow041_meanGapNumeratorChars geometryRow041_meanGapDenominatorChars
    (20250079 : Int) (26904000000 : Int)
    geometryRow041_meanGap_numerator_no_slash geometryRow041_meanGap_numerator_parse
    geometryRow041_meanGap_denominator_parse geometryRow041_meanGap_denominator_nonzero

theorem geometryRow041_meanGap_read :
    rationalField geometryRowsJson041 "mean_gap" = .ok geometryRowsTyped041.meanGap :=
  original_rationalField_of_string geometryRowsJson041 "mean_gap" geometryRow041_meanGapText
    geometryRowsTyped041.meanGap geometryRow041_meanGap_field geometryRow041_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_meanGap_complete"
  err.flush

noncomputable def geometryRow041_jensenBoundNumeratorChars : List Char := ['2', '5', '9', '0', '3', '8', '8', '4', '7', '2', '1', '7', '2', '4', '2', '1', '7', '0', '4', '3', '7', '4', '8', '2', '5', '8', '5', '1', '3', '8', '4', '4', '8', '4', '1', '1', '6', '6', '7', '8', '2', '6', '2', '5', '8', '6', '9', '3', '4', '7', '3', '6', '0', '3', '6', '1', '9', '5', '8', '4', '4', '4', '3', '8', '1', '5', '2', '8', '4', '4', '1', '5', '5', '3', '6', '4', '1', '3', '7', '1', '3', '4', '7', '9', '3', '0', '6', '9', '4', '7', '9', '2', '8', '8', '4', '2', '3', '2', '6', '3', '9', '5', '7', '1', '4', '1', '3', '7', '0', '2', '7', '8', '7', '5', '0', '2', '8', '7', '8', '4', '5', '2', '2', '4', '2', '5', '7', '4', '0', '8', '9', '4', '0', '1', '8', '9', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_jensenBoundDenominatorChars : List Char := ['8', '7', '5', '9', '6', '4', '0', '5', '0', '5', '2', '8', '6', '7', '3', '7', '5', '6', '5', '3', '9', '8', '5', '1', '5', '5', '5', '5', '8', '0', '0', '5', '4', '2', '6', '6', '4', '1', '9', '7', '1', '8', '5', '5', '8', '5', '8', '5', '6', '1', '8', '7', '1', '7', '0', '0', '8', '2', '4', '0', '7', '4', '5', '5', '2', '6', '4', '3', '5', '2', '1', '4', '7', '6', '2', '7', '7', '1', '1', '9', '6', '4', '9', '9', '6', '5', '7', '6', '3', '0', '0', '1', '7', '0', '1', '9', '9', '7', '1', '8', '6', '4', '2', '1', '9', '5', '8', '3', '0', '9', '7', '0', '8', '6', '5', '9', '9', '6', '6', '0', '0', '1', '4', '7', '0', '2', '1', '0', '6', '4', '7', '7', '7', '6', '3', '5', '2', '2', '4', '6', '2', '5', '3', '0', '9', '1', '8', '0', '8', '7', '5', '6', '1', '4', '2', '4', '7', '4', '5', '0', '7', '6', '9', '7', '3', '5', '0', '0', '3', '9', '3', '2', '9', '7', '9', '7', '4', '0', '1', '7']
noncomputable def geometryRow041_jensenBoundText : String := String.ofList (geometryRow041_jensenBoundNumeratorChars ++ '/' :: geometryRow041_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_jensenBound_before_field"
  err.flush

theorem geometryRow041_jensenBound_field :
    geometryRowsJson041.getObjVal? "jensen_bound" = .ok (.str geometryRow041_jensenBoundText) := by rfl

theorem geometryRow041_jensenBound_numerator_no_slash :
    geometryRow041_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow041_jensenBoundNumeratorChars = some (25903884721724217043748258513844841166782625869347360361958444381528441553641371347930694792884232639571413702787502878452242574089401894531250000000000000000000000 : Int) := by decide +kernel

theorem geometryRow041_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow041_jensenBoundDenominatorChars = some (875964050528673756539851555580054266419718558585618717008240745526435214762771196499657630017019971864219583097086599660014702106477763522462530918087561424745076973500393297974017 : Int) := by decide +kernel

theorem geometryRow041_jensenBound_denominator_nonzero : (875964050528673756539851555580054266419718558585618717008240745526435214762771196499657630017019971864219583097086599660014702106477763522462530918087561424745076973500393297974017 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_jensenBound_parse :
    parseRational geometryRow041_jensenBoundText = .ok geometryRowsTyped041.jensenBound :=
  original_rational_fraction_of_chars geometryRow041_jensenBoundNumeratorChars geometryRow041_jensenBoundDenominatorChars
    (25903884721724217043748258513844841166782625869347360361958444381528441553641371347930694792884232639571413702787502878452242574089401894531250000000000000000000000 : Int) (875964050528673756539851555580054266419718558585618717008240745526435214762771196499657630017019971864219583097086599660014702106477763522462530918087561424745076973500393297974017 : Int)
    geometryRow041_jensenBound_numerator_no_slash geometryRow041_jensenBound_numerator_parse
    geometryRow041_jensenBound_denominator_parse geometryRow041_jensenBound_denominator_nonzero

theorem geometryRow041_jensenBound_read :
    rationalField geometryRowsJson041 "jensen_bound" = .ok geometryRowsTyped041.jensenBound :=
  original_rationalField_of_string geometryRowsJson041 "jensen_bound" geometryRow041_jensenBoundText
    geometryRowsTyped041.jensenBound geometryRow041_jensenBound_field geometryRow041_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_factorMaxima_before"
  err.flush

theorem geometryRow041_factorMaxima_read :
    rationalArrayField geometryRowsJson041 "factor_maxima" = .ok geometryRowsTyped041.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_gapWeightedMeans_before"
  err.flush

theorem geometryRow041_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson041 "gap_weighted_means" = .ok geometryRowsTyped041.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow041_floorChars : List Char := ['2', '3', '4', '2', '9', '2', '3', '9', '9', '0', '1', '3', '9']
noncomputable def geometryRow041_floorText : String := String.ofList geometryRow041_floorChars

theorem geometryRow041_floor_text_read :
    geometryRowsJson041.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow041_floorText := by rfl

theorem geometryRow041_floor_chars_parse :
    SourceJson.intChars geometryRow041_floorChars = some (2342923990139 : Int) := by decide +kernel

theorem geometryRow041_floor_parse :
    parseInteger geometryRow041_floorText = .ok geometryRowsTyped041.jensenFloorQ96 := by
  simp only [geometryRow041_floorText, parseInteger, String.toList_ofList, geometryRow041_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_041 :
    decodeGeometryRow geometryRowsJson041 = .ok geometryRowsTyped041 :=
  original_geometryRow_of_fields geometryRowsJson041 geometryRowsTyped041 geometryRow041_floorText
    geometryRow041_simplexId_read geometryRow041_vertexIds_read
    geometryRow041_physicalVolume_read geometryRow041_meanGap_read
    geometryRow041_factorMaxima_read geometryRow041_gapWeightedMeans_read
    geometryRow041_jensenBound_read geometryRow041_floor_text_read geometryRow041_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_041_original_decoder_complete"
  err.flush

#print axioms geometryRow041_simplexId_read
#print axioms geometryRow041_vertexIds_read
#print axioms geometryRow041_physicalVolume_field
#print axioms geometryRow041_physicalVolume_numerator_no_slash
#print axioms geometryRow041_physicalVolume_numerator_parse
#print axioms geometryRow041_physicalVolume_denominator_parse
#print axioms geometryRow041_physicalVolume_denominator_nonzero
#print axioms geometryRow041_physicalVolume_parse
#print axioms geometryRow041_physicalVolume_read
#print axioms geometryRow041_meanGap_field
#print axioms geometryRow041_meanGap_numerator_no_slash
#print axioms geometryRow041_meanGap_numerator_parse
#print axioms geometryRow041_meanGap_denominator_parse
#print axioms geometryRow041_meanGap_denominator_nonzero
#print axioms geometryRow041_meanGap_parse
#print axioms geometryRow041_meanGap_read
#print axioms geometryRow041_jensenBound_field
#print axioms geometryRow041_jensenBound_numerator_no_slash
#print axioms geometryRow041_jensenBound_numerator_parse
#print axioms geometryRow041_jensenBound_denominator_parse
#print axioms geometryRow041_jensenBound_denominator_nonzero
#print axioms geometryRow041_jensenBound_parse
#print axioms geometryRow041_jensenBound_read
#print axioms geometryRow041_factorMaxima_read
#print axioms geometryRow041_gapWeightedMeans_read
#print axioms geometryRow041_floor_text_read
#print axioms geometryRow041_floor_chars_parse
#print axioms geometryRow041_floor_parse
#print axioms decode_geometry_Rows_041

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
