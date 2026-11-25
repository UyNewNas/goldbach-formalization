import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00700

/-! Original GeometryRow 31: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson031 : SourceJson :=
  (simplicesChunk031Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped031 : GeometryRow :=
  { simplexId := 31,
    vertexIds := #[27, 25, 23, 22, 8, 6, 5, 3, 1],
    physicalVolume := ((898221157283285002342251592538340967 : ℚ) / (30419289180000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((7229696297539 : ℚ) / (79480800000000 : ℚ)), ((7286874680479 : ℚ) / (79480800000000 : ℚ)), ((3249288387959 : ℚ) / (26493600000000 : ℚ)), ((72506343839 : ℚ) / (794808000000 : ℚ)), ((6800608059499 : ℚ) / (79480800000000 : ℚ)), ((1878344934601 : ℚ) / (26493600000000 : ℚ)), ((1402680205309 : ℚ) / (39740400000000 : ℚ)), ((273914195353 : ℚ) / (7948080000000 : ℚ)), ((2611762403617 : ℚ) / (79480800000000 : ℚ)), ((2611746507457 : ℚ) / (79480800000000 : ℚ))],
    jensenBound := ((909794148206942285966102184251804962969722854726794816988453029699464106498750068817920000000000000000000 : ℚ) / (14328100258724066744654495493041658089807547795860715384299874813589270796295094325294397635657028982102981788578488480343 : ℚ)),
    jensenFloorQ96 := (5030765930380 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_simplexId_before"
  err.flush

theorem geometryRow031_simplexId_read :
    geometryRowsJson031.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped031.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_vertexIds_before"
  err.flush

theorem geometryRow031_vertexIds_read :
    geometryRowsJson031.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped031.vertexIds := by decide +kernel

noncomputable def geometryRow031_physicalVolumeNumeratorChars : List Char := ['8', '9', '8', '2', '2', '1', '1', '5', '7', '2', '8', '3', '2', '8', '5', '0', '0', '2', '3', '4', '2', '2', '5', '1', '5', '9', '2', '5', '3', '8', '3', '4', '0', '9', '6', '7']
noncomputable def geometryRow031_physicalVolumeDenominatorChars : List Char := ['3', '0', '4', '1', '9', '2', '8', '9', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow031_physicalVolumeText : String := String.ofList (geometryRow031_physicalVolumeNumeratorChars ++ '/' :: geometryRow031_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_physicalVolume_before_field"
  err.flush

theorem geometryRow031_physicalVolume_field :
    geometryRowsJson031.getObjVal? "physical_volume" = .ok (.str geometryRow031_physicalVolumeText) := by rfl

theorem geometryRow031_physicalVolume_numerator_no_slash :
    geometryRow031_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow031_physicalVolumeNumeratorChars = some (898221157283285002342251592538340967 : Int) := by decide +kernel

theorem geometryRow031_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow031_physicalVolumeDenominatorChars = some (30419289180000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow031_physicalVolume_denominator_nonzero : (30419289180000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_physicalVolume_parse :
    parseRational geometryRow031_physicalVolumeText = .ok geometryRowsTyped031.physicalVolume :=
  original_rational_fraction_of_chars geometryRow031_physicalVolumeNumeratorChars geometryRow031_physicalVolumeDenominatorChars
    (898221157283285002342251592538340967 : Int) (30419289180000000000000000000000000000000000000000000000000000 : Int)
    geometryRow031_physicalVolume_numerator_no_slash geometryRow031_physicalVolume_numerator_parse
    geometryRow031_physicalVolume_denominator_parse geometryRow031_physicalVolume_denominator_nonzero

theorem geometryRow031_physicalVolume_read :
    rationalField geometryRowsJson031 "physical_volume" = .ok geometryRowsTyped031.physicalVolume :=
  original_rationalField_of_string geometryRowsJson031 "physical_volume" geometryRow031_physicalVolumeText
    geometryRowsTyped031.physicalVolume geometryRow031_physicalVolume_field geometryRow031_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_physicalVolume_complete"
  err.flush

noncomputable def geometryRow031_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow031_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow031_meanGapText : String := String.ofList (geometryRow031_meanGapNumeratorChars ++ '/' :: geometryRow031_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_meanGap_before_field"
  err.flush

theorem geometryRow031_meanGap_field :
    geometryRowsJson031.getObjVal? "mean_gap" = .ok (.str geometryRow031_meanGapText) := by rfl

theorem geometryRow031_meanGap_numerator_no_slash :
    geometryRow031_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_meanGap_numerator_parse :
    SourceJson.intChars geometryRow031_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow031_meanGap_denominator_parse :
    SourceJson.intChars geometryRow031_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow031_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_meanGap_parse :
    parseRational geometryRow031_meanGapText = .ok geometryRowsTyped031.meanGap :=
  original_rational_fraction_of_chars geometryRow031_meanGapNumeratorChars geometryRow031_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow031_meanGap_numerator_no_slash geometryRow031_meanGap_numerator_parse
    geometryRow031_meanGap_denominator_parse geometryRow031_meanGap_denominator_nonzero

theorem geometryRow031_meanGap_read :
    rationalField geometryRowsJson031 "mean_gap" = .ok geometryRowsTyped031.meanGap :=
  original_rationalField_of_string geometryRowsJson031 "mean_gap" geometryRow031_meanGapText
    geometryRowsTyped031.meanGap geometryRow031_meanGap_field geometryRow031_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_meanGap_complete"
  err.flush

noncomputable def geometryRow031_jensenBoundNumeratorChars : List Char := ['9', '0', '9', '7', '9', '4', '1', '4', '8', '2', '0', '6', '9', '4', '2', '2', '8', '5', '9', '6', '6', '1', '0', '2', '1', '8', '4', '2', '5', '1', '8', '0', '4', '9', '6', '2', '9', '6', '9', '7', '2', '2', '8', '5', '4', '7', '2', '6', '7', '9', '4', '8', '1', '6', '9', '8', '8', '4', '5', '3', '0', '2', '9', '6', '9', '9', '4', '6', '4', '1', '0', '6', '4', '9', '8', '7', '5', '0', '0', '6', '8', '8', '1', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow031_jensenBoundDenominatorChars : List Char := ['1', '4', '3', '2', '8', '1', '0', '0', '2', '5', '8', '7', '2', '4', '0', '6', '6', '7', '4', '4', '6', '5', '4', '4', '9', '5', '4', '9', '3', '0', '4', '1', '6', '5', '8', '0', '8', '9', '8', '0', '7', '5', '4', '7', '7', '9', '5', '8', '6', '0', '7', '1', '5', '3', '8', '4', '2', '9', '9', '8', '7', '4', '8', '1', '3', '5', '8', '9', '2', '7', '0', '7', '9', '6', '2', '9', '5', '0', '9', '4', '3', '2', '5', '2', '9', '4', '3', '9', '7', '6', '3', '5', '6', '5', '7', '0', '2', '8', '9', '8', '2', '1', '0', '2', '9', '8', '1', '7', '8', '8', '5', '7', '8', '4', '8', '8', '4', '8', '0', '3', '4', '3']
noncomputable def geometryRow031_jensenBoundText : String := String.ofList (geometryRow031_jensenBoundNumeratorChars ++ '/' :: geometryRow031_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_jensenBound_before_field"
  err.flush

theorem geometryRow031_jensenBound_field :
    geometryRowsJson031.getObjVal? "jensen_bound" = .ok (.str geometryRow031_jensenBoundText) := by rfl

theorem geometryRow031_jensenBound_numerator_no_slash :
    geometryRow031_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow031_jensenBoundNumeratorChars = some (909794148206942285966102184251804962969722854726794816988453029699464106498750068817920000000000000000000 : Int) := by decide +kernel

theorem geometryRow031_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow031_jensenBoundDenominatorChars = some (14328100258724066744654495493041658089807547795860715384299874813589270796295094325294397635657028982102981788578488480343 : Int) := by decide +kernel

theorem geometryRow031_jensenBound_denominator_nonzero : (14328100258724066744654495493041658089807547795860715384299874813589270796295094325294397635657028982102981788578488480343 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_jensenBound_parse :
    parseRational geometryRow031_jensenBoundText = .ok geometryRowsTyped031.jensenBound :=
  original_rational_fraction_of_chars geometryRow031_jensenBoundNumeratorChars geometryRow031_jensenBoundDenominatorChars
    (909794148206942285966102184251804962969722854726794816988453029699464106498750068817920000000000000000000 : Int) (14328100258724066744654495493041658089807547795860715384299874813589270796295094325294397635657028982102981788578488480343 : Int)
    geometryRow031_jensenBound_numerator_no_slash geometryRow031_jensenBound_numerator_parse
    geometryRow031_jensenBound_denominator_parse geometryRow031_jensenBound_denominator_nonzero

theorem geometryRow031_jensenBound_read :
    rationalField geometryRowsJson031 "jensen_bound" = .ok geometryRowsTyped031.jensenBound :=
  original_rationalField_of_string geometryRowsJson031 "jensen_bound" geometryRow031_jensenBoundText
    geometryRowsTyped031.jensenBound geometryRow031_jensenBound_field geometryRow031_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_factorMaxima_before"
  err.flush

theorem geometryRow031_factorMaxima_read :
    rationalArrayField geometryRowsJson031 "factor_maxima" = .ok geometryRowsTyped031.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_gapWeightedMeans_before"
  err.flush

theorem geometryRow031_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson031 "gap_weighted_means" = .ok geometryRowsTyped031.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow031_floorChars : List Char := ['5', '0', '3', '0', '7', '6', '5', '9', '3', '0', '3', '8', '0']
noncomputable def geometryRow031_floorText : String := String.ofList geometryRow031_floorChars

theorem geometryRow031_floor_text_read :
    geometryRowsJson031.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow031_floorText := by rfl

theorem geometryRow031_floor_chars_parse :
    SourceJson.intChars geometryRow031_floorChars = some (5030765930380 : Int) := by decide +kernel

theorem geometryRow031_floor_parse :
    parseInteger geometryRow031_floorText = .ok geometryRowsTyped031.jensenFloorQ96 := by
  simp only [geometryRow031_floorText, parseInteger, String.toList_ofList, geometryRow031_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_031 :
    decodeGeometryRow geometryRowsJson031 = .ok geometryRowsTyped031 :=
  original_geometryRow_of_fields geometryRowsJson031 geometryRowsTyped031 geometryRow031_floorText
    geometryRow031_simplexId_read geometryRow031_vertexIds_read
    geometryRow031_physicalVolume_read geometryRow031_meanGap_read
    geometryRow031_factorMaxima_read geometryRow031_gapWeightedMeans_read
    geometryRow031_jensenBound_read geometryRow031_floor_text_read geometryRow031_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_031_original_decoder_complete"
  err.flush

#print axioms geometryRow031_simplexId_read
#print axioms geometryRow031_vertexIds_read
#print axioms geometryRow031_physicalVolume_field
#print axioms geometryRow031_physicalVolume_numerator_no_slash
#print axioms geometryRow031_physicalVolume_numerator_parse
#print axioms geometryRow031_physicalVolume_denominator_parse
#print axioms geometryRow031_physicalVolume_denominator_nonzero
#print axioms geometryRow031_physicalVolume_parse
#print axioms geometryRow031_physicalVolume_read
#print axioms geometryRow031_meanGap_field
#print axioms geometryRow031_meanGap_numerator_no_slash
#print axioms geometryRow031_meanGap_numerator_parse
#print axioms geometryRow031_meanGap_denominator_parse
#print axioms geometryRow031_meanGap_denominator_nonzero
#print axioms geometryRow031_meanGap_parse
#print axioms geometryRow031_meanGap_read
#print axioms geometryRow031_jensenBound_field
#print axioms geometryRow031_jensenBound_numerator_no_slash
#print axioms geometryRow031_jensenBound_numerator_parse
#print axioms geometryRow031_jensenBound_denominator_parse
#print axioms geometryRow031_jensenBound_denominator_nonzero
#print axioms geometryRow031_jensenBound_parse
#print axioms geometryRow031_jensenBound_read
#print axioms geometryRow031_factorMaxima_read
#print axioms geometryRow031_gapWeightedMeans_read
#print axioms geometryRow031_floor_text_read
#print axioms geometryRow031_floor_chars_parse
#print axioms geometryRow031_floor_parse
#print axioms decode_geometry_Rows_031

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
