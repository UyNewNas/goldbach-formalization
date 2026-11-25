import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00000

/-! Original GeometryRow 0: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson000 : SourceJson :=
  (simplicesChunk000Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped000 : GeometryRow :=
  { simplexId := 0,
    vertexIds := #[27, 25, 11, 9, 7, 5, 3, 1, 0],
    physicalVolume := ((19739397832697952137558059616479938870079 : ℚ) / (455559274759680000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((16827881 : ℚ) / (180000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2729208052373 : ℚ) / (28701400000000 : ℚ)), ((343731975221 : ℚ) / (3587675000000 : ℚ)), ((62006907809983 : ℚ) / (516625200000000 : ℚ)), ((15260448353743 : ℚ) / (172208400000000 : ℚ)), ((14065087471927 : ℚ) / (172208400000000 : ℚ)), ((37981941979937 : ℚ) / (516625200000000 : ℚ)), ((9444658442381 : ℚ) / (258312600000000 : ℚ)), ((111973056431 : ℚ) / (3228907500000 : ℚ)), ((872045089711 : ℚ) / (25831260000000 : ℚ)), ((8484957488687 : ℚ) / (258312600000000 : ℚ))],
    jensenBound := ((10834690813210051893402338510123798599562269817407486088488213780293011258042147800259092050000000000000000000 : ℚ) / (127959917763745368475196527417819510952049770006681331846640501075257306822069892456899675389103890739359516969634488889416849 : ℚ)),
    jensenFloorQ96 := (6708449485921 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_simplexId_before"
  err.flush

theorem geometryRow000_simplexId_read :
    geometryRowsJson000.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped000.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_vertexIds_before"
  err.flush

theorem geometryRow000_vertexIds_read :
    geometryRowsJson000.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped000.vertexIds := by decide +kernel

noncomputable def geometryRow000_physicalVolumeNumeratorChars : List Char := ['1', '9', '7', '3', '9', '3', '9', '7', '8', '3', '2', '6', '9', '7', '9', '5', '2', '1', '3', '7', '5', '5', '8', '0', '5', '9', '6', '1', '6', '4', '7', '9', '9', '3', '8', '8', '7', '0', '0', '7', '9']
noncomputable def geometryRow000_physicalVolumeDenominatorChars : List Char := ['4', '5', '5', '5', '5', '9', '2', '7', '4', '7', '5', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_physicalVolumeText : String := String.ofList (geometryRow000_physicalVolumeNumeratorChars ++ '/' :: geometryRow000_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_physicalVolume_before_field"
  err.flush

theorem geometryRow000_physicalVolume_field :
    geometryRowsJson000.getObjVal? "physical_volume" = .ok (.str geometryRow000_physicalVolumeText) := by rfl

theorem geometryRow000_physicalVolume_numerator_no_slash :
    geometryRow000_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow000_physicalVolumeNumeratorChars = some (19739397832697952137558059616479938870079 : Int) := by decide +kernel

theorem geometryRow000_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow000_physicalVolumeDenominatorChars = some (455559274759680000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow000_physicalVolume_denominator_nonzero : (455559274759680000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_physicalVolume_parse :
    parseRational geometryRow000_physicalVolumeText = .ok geometryRowsTyped000.physicalVolume :=
  original_rational_fraction_of_chars geometryRow000_physicalVolumeNumeratorChars geometryRow000_physicalVolumeDenominatorChars
    (19739397832697952137558059616479938870079 : Int) (455559274759680000000000000000000000000000000000000000000000000000 : Int)
    geometryRow000_physicalVolume_numerator_no_slash geometryRow000_physicalVolume_numerator_parse
    geometryRow000_physicalVolume_denominator_parse geometryRow000_physicalVolume_denominator_nonzero

theorem geometryRow000_physicalVolume_read :
    rationalField geometryRowsJson000 "physical_volume" = .ok geometryRowsTyped000.physicalVolume :=
  original_rationalField_of_string geometryRowsJson000 "physical_volume" geometryRow000_physicalVolumeText
    geometryRowsTyped000.physicalVolume geometryRow000_physicalVolume_field geometryRow000_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_physicalVolume_complete"
  err.flush

noncomputable def geometryRow000_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow000_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_meanGapText : String := String.ofList (geometryRow000_meanGapNumeratorChars ++ '/' :: geometryRow000_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_meanGap_before_field"
  err.flush

theorem geometryRow000_meanGap_field :
    geometryRowsJson000.getObjVal? "mean_gap" = .ok (.str geometryRow000_meanGapText) := by rfl

theorem geometryRow000_meanGap_numerator_no_slash :
    geometryRow000_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_meanGap_numerator_parse :
    SourceJson.intChars geometryRow000_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow000_meanGap_denominator_parse :
    SourceJson.intChars geometryRow000_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow000_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_meanGap_parse :
    parseRational geometryRow000_meanGapText = .ok geometryRowsTyped000.meanGap :=
  original_rational_fraction_of_chars geometryRow000_meanGapNumeratorChars geometryRow000_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow000_meanGap_numerator_no_slash geometryRow000_meanGap_numerator_parse
    geometryRow000_meanGap_denominator_parse geometryRow000_meanGap_denominator_nonzero

theorem geometryRow000_meanGap_read :
    rationalField geometryRowsJson000 "mean_gap" = .ok geometryRowsTyped000.meanGap :=
  original_rationalField_of_string geometryRowsJson000 "mean_gap" geometryRow000_meanGapText
    geometryRowsTyped000.meanGap geometryRow000_meanGap_field geometryRow000_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_meanGap_complete"
  err.flush

noncomputable def geometryRow000_jensenBoundNumeratorChars : List Char := ['1', '0', '8', '3', '4', '6', '9', '0', '8', '1', '3', '2', '1', '0', '0', '5', '1', '8', '9', '3', '4', '0', '2', '3', '3', '8', '5', '1', '0', '1', '2', '3', '7', '9', '8', '5', '9', '9', '5', '6', '2', '2', '6', '9', '8', '1', '7', '4', '0', '7', '4', '8', '6', '0', '8', '8', '4', '8', '8', '2', '1', '3', '7', '8', '0', '2', '9', '3', '0', '1', '1', '2', '5', '8', '0', '4', '2', '1', '4', '7', '8', '0', '0', '2', '5', '9', '0', '9', '2', '0', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_jensenBoundDenominatorChars : List Char := ['1', '2', '7', '9', '5', '9', '9', '1', '7', '7', '6', '3', '7', '4', '5', '3', '6', '8', '4', '7', '5', '1', '9', '6', '5', '2', '7', '4', '1', '7', '8', '1', '9', '5', '1', '0', '9', '5', '2', '0', '4', '9', '7', '7', '0', '0', '0', '6', '6', '8', '1', '3', '3', '1', '8', '4', '6', '6', '4', '0', '5', '0', '1', '0', '7', '5', '2', '5', '7', '3', '0', '6', '8', '2', '2', '0', '6', '9', '8', '9', '2', '4', '5', '6', '8', '9', '9', '6', '7', '5', '3', '8', '9', '1', '0', '3', '8', '9', '0', '7', '3', '9', '3', '5', '9', '5', '1', '6', '9', '6', '9', '6', '3', '4', '4', '8', '8', '8', '8', '9', '4', '1', '6', '8', '4', '9']
noncomputable def geometryRow000_jensenBoundText : String := String.ofList (geometryRow000_jensenBoundNumeratorChars ++ '/' :: geometryRow000_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_jensenBound_before_field"
  err.flush

theorem geometryRow000_jensenBound_field :
    geometryRowsJson000.getObjVal? "jensen_bound" = .ok (.str geometryRow000_jensenBoundText) := by rfl

theorem geometryRow000_jensenBound_numerator_no_slash :
    geometryRow000_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow000_jensenBoundNumeratorChars = some (10834690813210051893402338510123798599562269817407486088488213780293011258042147800259092050000000000000000000 : Int) := by decide +kernel

theorem geometryRow000_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow000_jensenBoundDenominatorChars = some (127959917763745368475196527417819510952049770006681331846640501075257306822069892456899675389103890739359516969634488889416849 : Int) := by decide +kernel

theorem geometryRow000_jensenBound_denominator_nonzero : (127959917763745368475196527417819510952049770006681331846640501075257306822069892456899675389103890739359516969634488889416849 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_jensenBound_parse :
    parseRational geometryRow000_jensenBoundText = .ok geometryRowsTyped000.jensenBound :=
  original_rational_fraction_of_chars geometryRow000_jensenBoundNumeratorChars geometryRow000_jensenBoundDenominatorChars
    (10834690813210051893402338510123798599562269817407486088488213780293011258042147800259092050000000000000000000 : Int) (127959917763745368475196527417819510952049770006681331846640501075257306822069892456899675389103890739359516969634488889416849 : Int)
    geometryRow000_jensenBound_numerator_no_slash geometryRow000_jensenBound_numerator_parse
    geometryRow000_jensenBound_denominator_parse geometryRow000_jensenBound_denominator_nonzero

theorem geometryRow000_jensenBound_read :
    rationalField geometryRowsJson000 "jensen_bound" = .ok geometryRowsTyped000.jensenBound :=
  original_rationalField_of_string geometryRowsJson000 "jensen_bound" geometryRow000_jensenBoundText
    geometryRowsTyped000.jensenBound geometryRow000_jensenBound_field geometryRow000_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_factorMaxima_before"
  err.flush

theorem geometryRow000_factorMaxima_read :
    rationalArrayField geometryRowsJson000 "factor_maxima" = .ok geometryRowsTyped000.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_gapWeightedMeans_before"
  err.flush

theorem geometryRow000_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson000 "gap_weighted_means" = .ok geometryRowsTyped000.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow000_floorChars : List Char := ['6', '7', '0', '8', '4', '4', '9', '4', '8', '5', '9', '2', '1']
noncomputable def geometryRow000_floorText : String := String.ofList geometryRow000_floorChars

theorem geometryRow000_floor_text_read :
    geometryRowsJson000.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow000_floorText := by rfl

theorem geometryRow000_floor_chars_parse :
    SourceJson.intChars geometryRow000_floorChars = some (6708449485921 : Int) := by decide +kernel

theorem geometryRow000_floor_parse :
    parseInteger geometryRow000_floorText = .ok geometryRowsTyped000.jensenFloorQ96 := by
  simp only [geometryRow000_floorText, parseInteger, String.toList_ofList, geometryRow000_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_000 :
    decodeGeometryRow geometryRowsJson000 = .ok geometryRowsTyped000 :=
  original_geometryRow_of_fields geometryRowsJson000 geometryRowsTyped000 geometryRow000_floorText
    geometryRow000_simplexId_read geometryRow000_vertexIds_read
    geometryRow000_physicalVolume_read geometryRow000_meanGap_read
    geometryRow000_factorMaxima_read geometryRow000_gapWeightedMeans_read
    geometryRow000_jensenBound_read geometryRow000_floor_text_read geometryRow000_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_000_original_decoder_complete"
  err.flush

#print axioms geometryRow000_simplexId_read
#print axioms geometryRow000_vertexIds_read
#print axioms geometryRow000_physicalVolume_field
#print axioms geometryRow000_physicalVolume_numerator_no_slash
#print axioms geometryRow000_physicalVolume_numerator_parse
#print axioms geometryRow000_physicalVolume_denominator_parse
#print axioms geometryRow000_physicalVolume_denominator_nonzero
#print axioms geometryRow000_physicalVolume_parse
#print axioms geometryRow000_physicalVolume_read
#print axioms geometryRow000_meanGap_field
#print axioms geometryRow000_meanGap_numerator_no_slash
#print axioms geometryRow000_meanGap_numerator_parse
#print axioms geometryRow000_meanGap_denominator_parse
#print axioms geometryRow000_meanGap_denominator_nonzero
#print axioms geometryRow000_meanGap_parse
#print axioms geometryRow000_meanGap_read
#print axioms geometryRow000_jensenBound_field
#print axioms geometryRow000_jensenBound_numerator_no_slash
#print axioms geometryRow000_jensenBound_numerator_parse
#print axioms geometryRow000_jensenBound_denominator_parse
#print axioms geometryRow000_jensenBound_denominator_nonzero
#print axioms geometryRow000_jensenBound_parse
#print axioms geometryRow000_jensenBound_read
#print axioms geometryRow000_factorMaxima_read
#print axioms geometryRow000_gapWeightedMeans_read
#print axioms geometryRow000_floor_text_read
#print axioms geometryRow000_floor_chars_parse
#print axioms geometryRow000_floor_parse
#print axioms decode_geometry_Rows_000

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
