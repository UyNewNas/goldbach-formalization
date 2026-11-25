import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00800

/-! Original GeometryRow 33: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson033 : SourceJson :=
  (simplicesChunk033Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped033 : GeometryRow :=
  { simplexId := 33,
    vertexIds := #[27, 25, 23, 22, 21, 19, 5, 3, 1],
    physicalVolume := ((1121338426867929603335887626773 : ℚ) / (79850634097500000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((3554980534829 : ℚ) / (39740400000000 : ℚ)), ((3583569726299 : ℚ) / (39740400000000 : ℚ)), ((661117977371 : ℚ) / (5298720000000 : ℚ)), ((7531876574939 : ℚ) / (79480800000000 : ℚ)), ((7064606715931 : ℚ) / (79480800000000 : ℚ)), ((51855680803 : ℚ) / (756960000000 : ℚ)), ((193590446491 : ℚ) / (5677200000000 : ℚ)), ((188860556699 : ℚ) / (5677200000000 : ℚ)), ((1249712354633 : ℚ) / (39740400000000 : ℚ)), ((1249704406553 : ℚ) / (39740400000000 : ℚ))],
    jensenBound := ((45727888365735657703031769523432424934525820842994828938408143061137884604006400000000000000000000000000 : ℚ) / (1326973131164420240842407995944239947149307431671972471469634586241717268143609659974303310379221606922644155763334956287 : ℚ)),
    jensenFloorQ96 := (2730226020247 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_simplexId_before"
  err.flush

theorem geometryRow033_simplexId_read :
    geometryRowsJson033.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped033.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_vertexIds_before"
  err.flush

theorem geometryRow033_vertexIds_read :
    geometryRowsJson033.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped033.vertexIds := by decide +kernel

noncomputable def geometryRow033_physicalVolumeNumeratorChars : List Char := ['1', '1', '2', '1', '3', '3', '8', '4', '2', '6', '8', '6', '7', '9', '2', '9', '6', '0', '3', '3', '3', '5', '8', '8', '7', '6', '2', '6', '7', '7', '3']
noncomputable def geometryRow033_physicalVolumeDenominatorChars : List Char := ['7', '9', '8', '5', '0', '6', '3', '4', '0', '9', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_physicalVolumeText : String := String.ofList (geometryRow033_physicalVolumeNumeratorChars ++ '/' :: geometryRow033_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_physicalVolume_before_field"
  err.flush

theorem geometryRow033_physicalVolume_field :
    geometryRowsJson033.getObjVal? "physical_volume" = .ok (.str geometryRow033_physicalVolumeText) := by rfl

theorem geometryRow033_physicalVolume_numerator_no_slash :
    geometryRow033_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow033_physicalVolumeNumeratorChars = some (1121338426867929603335887626773 : Int) := by decide +kernel

theorem geometryRow033_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow033_physicalVolumeDenominatorChars = some (79850634097500000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow033_physicalVolume_denominator_nonzero : (79850634097500000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_physicalVolume_parse :
    parseRational geometryRow033_physicalVolumeText = .ok geometryRowsTyped033.physicalVolume :=
  original_rational_fraction_of_chars geometryRow033_physicalVolumeNumeratorChars geometryRow033_physicalVolumeDenominatorChars
    (1121338426867929603335887626773 : Int) (79850634097500000000000000000000000000000000000000000000 : Int)
    geometryRow033_physicalVolume_numerator_no_slash geometryRow033_physicalVolume_numerator_parse
    geometryRow033_physicalVolume_denominator_parse geometryRow033_physicalVolume_denominator_nonzero

theorem geometryRow033_physicalVolume_read :
    rationalField geometryRowsJson033 "physical_volume" = .ok geometryRowsTyped033.physicalVolume :=
  original_rationalField_of_string geometryRowsJson033 "physical_volume" geometryRow033_physicalVolumeText
    geometryRowsTyped033.physicalVolume geometryRow033_physicalVolume_field geometryRow033_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_physicalVolume_complete"
  err.flush

noncomputable def geometryRow033_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow033_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_meanGapText : String := String.ofList (geometryRow033_meanGapNumeratorChars ++ '/' :: geometryRow033_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_meanGap_before_field"
  err.flush

theorem geometryRow033_meanGap_field :
    geometryRowsJson033.getObjVal? "mean_gap" = .ok (.str geometryRow033_meanGapText) := by rfl

theorem geometryRow033_meanGap_numerator_no_slash :
    geometryRow033_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_meanGap_numerator_parse :
    SourceJson.intChars geometryRow033_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow033_meanGap_denominator_parse :
    SourceJson.intChars geometryRow033_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow033_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_meanGap_parse :
    parseRational geometryRow033_meanGapText = .ok geometryRowsTyped033.meanGap :=
  original_rational_fraction_of_chars geometryRow033_meanGapNumeratorChars geometryRow033_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow033_meanGap_numerator_no_slash geometryRow033_meanGap_numerator_parse
    geometryRow033_meanGap_denominator_parse geometryRow033_meanGap_denominator_nonzero

theorem geometryRow033_meanGap_read :
    rationalField geometryRowsJson033 "mean_gap" = .ok geometryRowsTyped033.meanGap :=
  original_rationalField_of_string geometryRowsJson033 "mean_gap" geometryRow033_meanGapText
    geometryRowsTyped033.meanGap geometryRow033_meanGap_field geometryRow033_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_meanGap_complete"
  err.flush

noncomputable def geometryRow033_jensenBoundNumeratorChars : List Char := ['4', '5', '7', '2', '7', '8', '8', '8', '3', '6', '5', '7', '3', '5', '6', '5', '7', '7', '0', '3', '0', '3', '1', '7', '6', '9', '5', '2', '3', '4', '3', '2', '4', '2', '4', '9', '3', '4', '5', '2', '5', '8', '2', '0', '8', '4', '2', '9', '9', '4', '8', '2', '8', '9', '3', '8', '4', '0', '8', '1', '4', '3', '0', '6', '1', '1', '3', '7', '8', '8', '4', '6', '0', '4', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_jensenBoundDenominatorChars : List Char := ['1', '3', '2', '6', '9', '7', '3', '1', '3', '1', '1', '6', '4', '4', '2', '0', '2', '4', '0', '8', '4', '2', '4', '0', '7', '9', '9', '5', '9', '4', '4', '2', '3', '9', '9', '4', '7', '1', '4', '9', '3', '0', '7', '4', '3', '1', '6', '7', '1', '9', '7', '2', '4', '7', '1', '4', '6', '9', '6', '3', '4', '5', '8', '6', '2', '4', '1', '7', '1', '7', '2', '6', '8', '1', '4', '3', '6', '0', '9', '6', '5', '9', '9', '7', '4', '3', '0', '3', '3', '1', '0', '3', '7', '9', '2', '2', '1', '6', '0', '6', '9', '2', '2', '6', '4', '4', '1', '5', '5', '7', '6', '3', '3', '3', '4', '9', '5', '6', '2', '8', '7']
noncomputable def geometryRow033_jensenBoundText : String := String.ofList (geometryRow033_jensenBoundNumeratorChars ++ '/' :: geometryRow033_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_jensenBound_before_field"
  err.flush

theorem geometryRow033_jensenBound_field :
    geometryRowsJson033.getObjVal? "jensen_bound" = .ok (.str geometryRow033_jensenBoundText) := by rfl

theorem geometryRow033_jensenBound_numerator_no_slash :
    geometryRow033_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow033_jensenBoundNumeratorChars = some (45727888365735657703031769523432424934525820842994828938408143061137884604006400000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow033_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow033_jensenBoundDenominatorChars = some (1326973131164420240842407995944239947149307431671972471469634586241717268143609659974303310379221606922644155763334956287 : Int) := by decide +kernel

theorem geometryRow033_jensenBound_denominator_nonzero : (1326973131164420240842407995944239947149307431671972471469634586241717268143609659974303310379221606922644155763334956287 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_jensenBound_parse :
    parseRational geometryRow033_jensenBoundText = .ok geometryRowsTyped033.jensenBound :=
  original_rational_fraction_of_chars geometryRow033_jensenBoundNumeratorChars geometryRow033_jensenBoundDenominatorChars
    (45727888365735657703031769523432424934525820842994828938408143061137884604006400000000000000000000000000 : Int) (1326973131164420240842407995944239947149307431671972471469634586241717268143609659974303310379221606922644155763334956287 : Int)
    geometryRow033_jensenBound_numerator_no_slash geometryRow033_jensenBound_numerator_parse
    geometryRow033_jensenBound_denominator_parse geometryRow033_jensenBound_denominator_nonzero

theorem geometryRow033_jensenBound_read :
    rationalField geometryRowsJson033 "jensen_bound" = .ok geometryRowsTyped033.jensenBound :=
  original_rationalField_of_string geometryRowsJson033 "jensen_bound" geometryRow033_jensenBoundText
    geometryRowsTyped033.jensenBound geometryRow033_jensenBound_field geometryRow033_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_factorMaxima_before"
  err.flush

theorem geometryRow033_factorMaxima_read :
    rationalArrayField geometryRowsJson033 "factor_maxima" = .ok geometryRowsTyped033.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_gapWeightedMeans_before"
  err.flush

theorem geometryRow033_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson033 "gap_weighted_means" = .ok geometryRowsTyped033.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow033_floorChars : List Char := ['2', '7', '3', '0', '2', '2', '6', '0', '2', '0', '2', '4', '7']
noncomputable def geometryRow033_floorText : String := String.ofList geometryRow033_floorChars

theorem geometryRow033_floor_text_read :
    geometryRowsJson033.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow033_floorText := by rfl

theorem geometryRow033_floor_chars_parse :
    SourceJson.intChars geometryRow033_floorChars = some (2730226020247 : Int) := by decide +kernel

theorem geometryRow033_floor_parse :
    parseInteger geometryRow033_floorText = .ok geometryRowsTyped033.jensenFloorQ96 := by
  simp only [geometryRow033_floorText, parseInteger, String.toList_ofList, geometryRow033_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_033 :
    decodeGeometryRow geometryRowsJson033 = .ok geometryRowsTyped033 :=
  original_geometryRow_of_fields geometryRowsJson033 geometryRowsTyped033 geometryRow033_floorText
    geometryRow033_simplexId_read geometryRow033_vertexIds_read
    geometryRow033_physicalVolume_read geometryRow033_meanGap_read
    geometryRow033_factorMaxima_read geometryRow033_gapWeightedMeans_read
    geometryRow033_jensenBound_read geometryRow033_floor_text_read geometryRow033_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_033_original_decoder_complete"
  err.flush

#print axioms geometryRow033_simplexId_read
#print axioms geometryRow033_vertexIds_read
#print axioms geometryRow033_physicalVolume_field
#print axioms geometryRow033_physicalVolume_numerator_no_slash
#print axioms geometryRow033_physicalVolume_numerator_parse
#print axioms geometryRow033_physicalVolume_denominator_parse
#print axioms geometryRow033_physicalVolume_denominator_nonzero
#print axioms geometryRow033_physicalVolume_parse
#print axioms geometryRow033_physicalVolume_read
#print axioms geometryRow033_meanGap_field
#print axioms geometryRow033_meanGap_numerator_no_slash
#print axioms geometryRow033_meanGap_numerator_parse
#print axioms geometryRow033_meanGap_denominator_parse
#print axioms geometryRow033_meanGap_denominator_nonzero
#print axioms geometryRow033_meanGap_parse
#print axioms geometryRow033_meanGap_read
#print axioms geometryRow033_jensenBound_field
#print axioms geometryRow033_jensenBound_numerator_no_slash
#print axioms geometryRow033_jensenBound_numerator_parse
#print axioms geometryRow033_jensenBound_denominator_parse
#print axioms geometryRow033_jensenBound_denominator_nonzero
#print axioms geometryRow033_jensenBound_parse
#print axioms geometryRow033_jensenBound_read
#print axioms geometryRow033_factorMaxima_read
#print axioms geometryRow033_gapWeightedMeans_read
#print axioms geometryRow033_floor_text_read
#print axioms geometryRow033_floor_chars_parse
#print axioms geometryRow033_floor_parse
#print axioms decode_geometry_Rows_033

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
