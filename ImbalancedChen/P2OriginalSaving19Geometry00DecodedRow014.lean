import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00300

/-! Original GeometryRow 14: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson014 : SourceJson :=
  (simplicesChunk014Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped014 : GeometryRow :=
  { simplexId := 14,
    vertexIds := #[27, 25, 23, 21, 9, 8, 5, 3, 1],
    physicalVolume := ((2265112760361167534055782662090937996063 : ℚ) / (8555425081875000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((7287270422819 : ℚ) / (79480800000000 : ℚ)), ((7344448805759 : ℚ) / (79480800000000 : ℚ)), ((9733470307877 : ℚ) / (79480800000000 : ℚ)), ((918081798233 : ℚ) / (9935100000000 : ℚ)), ((6779015775499 : ℚ) / (79480800000000 : ℚ)), ((5649429659803 : ℚ) / (79480800000000 : ℚ)), ((1406278919309 : ℚ) / (39740400000000 : ℚ)), ((30514882017 : ℚ) / (883120000000 : ℚ)), ((858593520779 : ℚ) / (26493600000000 : ℚ)), ((2503331649493 : ℚ) / (79480800000000 : ℚ))],
    jensenBound := ((390684930394069789246969825882301326705445728009422557193409334483008467657139943374848000000000000000000000 : ℚ) / (669601376837514656547413069777686693515520052186569956427682705742364263483519065306818115873769044927095561864183487089 : ℚ)),
    jensenFloorQ96 := (46226382184764416 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_simplexId_before"
  err.flush

theorem geometryRow014_simplexId_read :
    geometryRowsJson014.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped014.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_vertexIds_before"
  err.flush

theorem geometryRow014_vertexIds_read :
    geometryRowsJson014.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped014.vertexIds := by decide +kernel

noncomputable def geometryRow014_physicalVolumeNumeratorChars : List Char := ['2', '2', '6', '5', '1', '1', '2', '7', '6', '0', '3', '6', '1', '1', '6', '7', '5', '3', '4', '0', '5', '5', '7', '8', '2', '6', '6', '2', '0', '9', '0', '9', '3', '7', '9', '9', '6', '0', '6', '3']
noncomputable def geometryRow014_physicalVolumeDenominatorChars : List Char := ['8', '5', '5', '5', '4', '2', '5', '0', '8', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_physicalVolumeText : String := String.ofList (geometryRow014_physicalVolumeNumeratorChars ++ '/' :: geometryRow014_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_physicalVolume_before_field"
  err.flush

theorem geometryRow014_physicalVolume_field :
    geometryRowsJson014.getObjVal? "physical_volume" = .ok (.str geometryRow014_physicalVolumeText) := by rfl

theorem geometryRow014_physicalVolume_numerator_no_slash :
    geometryRow014_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow014_physicalVolumeNumeratorChars = some (2265112760361167534055782662090937996063 : Int) := by decide +kernel

theorem geometryRow014_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow014_physicalVolumeDenominatorChars = some (8555425081875000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow014_physicalVolume_denominator_nonzero : (8555425081875000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_physicalVolume_parse :
    parseRational geometryRow014_physicalVolumeText = .ok geometryRowsTyped014.physicalVolume :=
  original_rational_fraction_of_chars geometryRow014_physicalVolumeNumeratorChars geometryRow014_physicalVolumeDenominatorChars
    (2265112760361167534055782662090937996063 : Int) (8555425081875000000000000000000000000000000000000000000000000 : Int)
    geometryRow014_physicalVolume_numerator_no_slash geometryRow014_physicalVolume_numerator_parse
    geometryRow014_physicalVolume_denominator_parse geometryRow014_physicalVolume_denominator_nonzero

theorem geometryRow014_physicalVolume_read :
    rationalField geometryRowsJson014 "physical_volume" = .ok geometryRowsTyped014.physicalVolume :=
  original_rationalField_of_string geometryRowsJson014 "physical_volume" geometryRow014_physicalVolumeText
    geometryRowsTyped014.physicalVolume geometryRow014_physicalVolume_field geometryRow014_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_physicalVolume_complete"
  err.flush

noncomputable def geometryRow014_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow014_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_meanGapText : String := String.ofList (geometryRow014_meanGapNumeratorChars ++ '/' :: geometryRow014_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_meanGap_before_field"
  err.flush

theorem geometryRow014_meanGap_field :
    geometryRowsJson014.getObjVal? "mean_gap" = .ok (.str geometryRow014_meanGapText) := by rfl

theorem geometryRow014_meanGap_numerator_no_slash :
    geometryRow014_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_meanGap_numerator_parse :
    SourceJson.intChars geometryRow014_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow014_meanGap_denominator_parse :
    SourceJson.intChars geometryRow014_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow014_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_meanGap_parse :
    parseRational geometryRow014_meanGapText = .ok geometryRowsTyped014.meanGap :=
  original_rational_fraction_of_chars geometryRow014_meanGapNumeratorChars geometryRow014_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow014_meanGap_numerator_no_slash geometryRow014_meanGap_numerator_parse
    geometryRow014_meanGap_denominator_parse geometryRow014_meanGap_denominator_nonzero

theorem geometryRow014_meanGap_read :
    rationalField geometryRowsJson014 "mean_gap" = .ok geometryRowsTyped014.meanGap :=
  original_rationalField_of_string geometryRowsJson014 "mean_gap" geometryRow014_meanGapText
    geometryRowsTyped014.meanGap geometryRow014_meanGap_field geometryRow014_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_meanGap_complete"
  err.flush

noncomputable def geometryRow014_jensenBoundNumeratorChars : List Char := ['3', '9', '0', '6', '8', '4', '9', '3', '0', '3', '9', '4', '0', '6', '9', '7', '8', '9', '2', '4', '6', '9', '6', '9', '8', '2', '5', '8', '8', '2', '3', '0', '1', '3', '2', '6', '7', '0', '5', '4', '4', '5', '7', '2', '8', '0', '0', '9', '4', '2', '2', '5', '5', '7', '1', '9', '3', '4', '0', '9', '3', '3', '4', '4', '8', '3', '0', '0', '8', '4', '6', '7', '6', '5', '7', '1', '3', '9', '9', '4', '3', '3', '7', '4', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_jensenBoundDenominatorChars : List Char := ['6', '6', '9', '6', '0', '1', '3', '7', '6', '8', '3', '7', '5', '1', '4', '6', '5', '6', '5', '4', '7', '4', '1', '3', '0', '6', '9', '7', '7', '7', '6', '8', '6', '6', '9', '3', '5', '1', '5', '5', '2', '0', '0', '5', '2', '1', '8', '6', '5', '6', '9', '9', '5', '6', '4', '2', '7', '6', '8', '2', '7', '0', '5', '7', '4', '2', '3', '6', '4', '2', '6', '3', '4', '8', '3', '5', '1', '9', '0', '6', '5', '3', '0', '6', '8', '1', '8', '1', '1', '5', '8', '7', '3', '7', '6', '9', '0', '4', '4', '9', '2', '7', '0', '9', '5', '5', '6', '1', '8', '6', '4', '1', '8', '3', '4', '8', '7', '0', '8', '9']
noncomputable def geometryRow014_jensenBoundText : String := String.ofList (geometryRow014_jensenBoundNumeratorChars ++ '/' :: geometryRow014_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_jensenBound_before_field"
  err.flush

theorem geometryRow014_jensenBound_field :
    geometryRowsJson014.getObjVal? "jensen_bound" = .ok (.str geometryRow014_jensenBoundText) := by rfl

theorem geometryRow014_jensenBound_numerator_no_slash :
    geometryRow014_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow014_jensenBoundNumeratorChars = some (390684930394069789246969825882301326705445728009422557193409334483008467657139943374848000000000000000000000 : Int) := by decide +kernel

theorem geometryRow014_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow014_jensenBoundDenominatorChars = some (669601376837514656547413069777686693515520052186569956427682705742364263483519065306818115873769044927095561864183487089 : Int) := by decide +kernel

theorem geometryRow014_jensenBound_denominator_nonzero : (669601376837514656547413069777686693515520052186569956427682705742364263483519065306818115873769044927095561864183487089 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_jensenBound_parse :
    parseRational geometryRow014_jensenBoundText = .ok geometryRowsTyped014.jensenBound :=
  original_rational_fraction_of_chars geometryRow014_jensenBoundNumeratorChars geometryRow014_jensenBoundDenominatorChars
    (390684930394069789246969825882301326705445728009422557193409334483008467657139943374848000000000000000000000 : Int) (669601376837514656547413069777686693515520052186569956427682705742364263483519065306818115873769044927095561864183487089 : Int)
    geometryRow014_jensenBound_numerator_no_slash geometryRow014_jensenBound_numerator_parse
    geometryRow014_jensenBound_denominator_parse geometryRow014_jensenBound_denominator_nonzero

theorem geometryRow014_jensenBound_read :
    rationalField geometryRowsJson014 "jensen_bound" = .ok geometryRowsTyped014.jensenBound :=
  original_rationalField_of_string geometryRowsJson014 "jensen_bound" geometryRow014_jensenBoundText
    geometryRowsTyped014.jensenBound geometryRow014_jensenBound_field geometryRow014_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_factorMaxima_before"
  err.flush

theorem geometryRow014_factorMaxima_read :
    rationalArrayField geometryRowsJson014 "factor_maxima" = .ok geometryRowsTyped014.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_gapWeightedMeans_before"
  err.flush

theorem geometryRow014_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson014 "gap_weighted_means" = .ok geometryRowsTyped014.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow014_floorChars : List Char := ['4', '6', '2', '2', '6', '3', '8', '2', '1', '8', '4', '7', '6', '4', '4', '1', '6']
noncomputable def geometryRow014_floorText : String := String.ofList geometryRow014_floorChars

theorem geometryRow014_floor_text_read :
    geometryRowsJson014.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow014_floorText := by rfl

theorem geometryRow014_floor_chars_parse :
    SourceJson.intChars geometryRow014_floorChars = some (46226382184764416 : Int) := by decide +kernel

theorem geometryRow014_floor_parse :
    parseInteger geometryRow014_floorText = .ok geometryRowsTyped014.jensenFloorQ96 := by
  simp only [geometryRow014_floorText, parseInteger, String.toList_ofList, geometryRow014_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_014 :
    decodeGeometryRow geometryRowsJson014 = .ok geometryRowsTyped014 :=
  original_geometryRow_of_fields geometryRowsJson014 geometryRowsTyped014 geometryRow014_floorText
    geometryRow014_simplexId_read geometryRow014_vertexIds_read
    geometryRow014_physicalVolume_read geometryRow014_meanGap_read
    geometryRow014_factorMaxima_read geometryRow014_gapWeightedMeans_read
    geometryRow014_jensenBound_read geometryRow014_floor_text_read geometryRow014_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_014_original_decoder_complete"
  err.flush

#print axioms geometryRow014_simplexId_read
#print axioms geometryRow014_vertexIds_read
#print axioms geometryRow014_physicalVolume_field
#print axioms geometryRow014_physicalVolume_numerator_no_slash
#print axioms geometryRow014_physicalVolume_numerator_parse
#print axioms geometryRow014_physicalVolume_denominator_parse
#print axioms geometryRow014_physicalVolume_denominator_nonzero
#print axioms geometryRow014_physicalVolume_parse
#print axioms geometryRow014_physicalVolume_read
#print axioms geometryRow014_meanGap_field
#print axioms geometryRow014_meanGap_numerator_no_slash
#print axioms geometryRow014_meanGap_numerator_parse
#print axioms geometryRow014_meanGap_denominator_parse
#print axioms geometryRow014_meanGap_denominator_nonzero
#print axioms geometryRow014_meanGap_parse
#print axioms geometryRow014_meanGap_read
#print axioms geometryRow014_jensenBound_field
#print axioms geometryRow014_jensenBound_numerator_no_slash
#print axioms geometryRow014_jensenBound_numerator_parse
#print axioms geometryRow014_jensenBound_denominator_parse
#print axioms geometryRow014_jensenBound_denominator_nonzero
#print axioms geometryRow014_jensenBound_parse
#print axioms geometryRow014_jensenBound_read
#print axioms geometryRow014_factorMaxima_read
#print axioms geometryRow014_gapWeightedMeans_read
#print axioms geometryRow014_floor_text_read
#print axioms geometryRow014_floor_chars_parse
#print axioms geometryRow014_floor_parse
#print axioms decode_geometry_Rows_014

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
