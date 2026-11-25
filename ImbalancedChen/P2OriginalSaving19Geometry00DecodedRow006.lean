import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00100

/-! Original GeometryRow 6: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson006 : SourceJson :=
  (simplicesChunk006Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped006 : GeometryRow :=
  { simplexId := 6,
    vertexIds := #[27, 25, 23, 9, 7, 5, 3, 1, 0],
    physicalVolume := ((8084384706297358632336870936183754063 : ℚ) / (205330201965000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((1846869134219 : ℚ) / (19870200000000 : ℚ)), ((930581864977 : ℚ) / (9935100000000 : ℚ)), ((1604380702007 : ℚ) / (13246800000000 : ℚ)), ((1188606422341 : ℚ) / (13246800000000 : ℚ)), ((370194664193 : ℚ) / (4415600000000 : ℚ)), ((959435959273 : ℚ) / (13246800000000 : ℚ)), ((117536815117 : ℚ) / (3311700000000 : ℚ)), ((68866627643 : ℚ) / (1987020000000 : ℚ)), ((33520261447 : ℚ) / (993510000000 : ℚ)), ((217430117123 : ℚ) / (6623400000000 : ℚ))],
    jensenBound := ((51938025064135906052354565795679157393700433704616872520779386736203370752614400000000000000000000 : ℚ) / (645836759066214920495108098985292859579998667154775296903695545110611366676326311462720183878091380551975784475063 : ℚ)),
    jensenFloorQ96 := (6371508330372 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_simplexId_before"
  err.flush

theorem geometryRow006_simplexId_read :
    geometryRowsJson006.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped006.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_vertexIds_before"
  err.flush

theorem geometryRow006_vertexIds_read :
    geometryRowsJson006.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped006.vertexIds := by decide +kernel

noncomputable def geometryRow006_physicalVolumeNumeratorChars : List Char := ['8', '0', '8', '4', '3', '8', '4', '7', '0', '6', '2', '9', '7', '3', '5', '8', '6', '3', '2', '3', '3', '6', '8', '7', '0', '9', '3', '6', '1', '8', '3', '7', '5', '4', '0', '6', '3']
noncomputable def geometryRow006_physicalVolumeDenominatorChars : List Char := ['2', '0', '5', '3', '3', '0', '2', '0', '1', '9', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_physicalVolumeText : String := String.ofList (geometryRow006_physicalVolumeNumeratorChars ++ '/' :: geometryRow006_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_physicalVolume_before_field"
  err.flush

theorem geometryRow006_physicalVolume_field :
    geometryRowsJson006.getObjVal? "physical_volume" = .ok (.str geometryRow006_physicalVolumeText) := by rfl

theorem geometryRow006_physicalVolume_numerator_no_slash :
    geometryRow006_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow006_physicalVolumeNumeratorChars = some (8084384706297358632336870936183754063 : Int) := by decide +kernel

theorem geometryRow006_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow006_physicalVolumeDenominatorChars = some (205330201965000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow006_physicalVolume_denominator_nonzero : (205330201965000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_physicalVolume_parse :
    parseRational geometryRow006_physicalVolumeText = .ok geometryRowsTyped006.physicalVolume :=
  original_rational_fraction_of_chars geometryRow006_physicalVolumeNumeratorChars geometryRow006_physicalVolumeDenominatorChars
    (8084384706297358632336870936183754063 : Int) (205330201965000000000000000000000000000000000000000000000000000 : Int)
    geometryRow006_physicalVolume_numerator_no_slash geometryRow006_physicalVolume_numerator_parse
    geometryRow006_physicalVolume_denominator_parse geometryRow006_physicalVolume_denominator_nonzero

theorem geometryRow006_physicalVolume_read :
    rationalField geometryRowsJson006 "physical_volume" = .ok geometryRowsTyped006.physicalVolume :=
  original_rationalField_of_string geometryRowsJson006 "physical_volume" geometryRow006_physicalVolumeText
    geometryRowsTyped006.physicalVolume geometryRow006_physicalVolume_field geometryRow006_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_physicalVolume_complete"
  err.flush

noncomputable def geometryRow006_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow006_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_meanGapText : String := String.ofList (geometryRow006_meanGapNumeratorChars ++ '/' :: geometryRow006_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_meanGap_before_field"
  err.flush

theorem geometryRow006_meanGap_field :
    geometryRowsJson006.getObjVal? "mean_gap" = .ok (.str geometryRow006_meanGapText) := by rfl

theorem geometryRow006_meanGap_numerator_no_slash :
    geometryRow006_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_meanGap_numerator_parse :
    SourceJson.intChars geometryRow006_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow006_meanGap_denominator_parse :
    SourceJson.intChars geometryRow006_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow006_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_meanGap_parse :
    parseRational geometryRow006_meanGapText = .ok geometryRowsTyped006.meanGap :=
  original_rational_fraction_of_chars geometryRow006_meanGapNumeratorChars geometryRow006_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow006_meanGap_numerator_no_slash geometryRow006_meanGap_numerator_parse
    geometryRow006_meanGap_denominator_parse geometryRow006_meanGap_denominator_nonzero

theorem geometryRow006_meanGap_read :
    rationalField geometryRowsJson006 "mean_gap" = .ok geometryRowsTyped006.meanGap :=
  original_rationalField_of_string geometryRowsJson006 "mean_gap" geometryRow006_meanGapText
    geometryRowsTyped006.meanGap geometryRow006_meanGap_field geometryRow006_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_meanGap_complete"
  err.flush

noncomputable def geometryRow006_jensenBoundNumeratorChars : List Char := ['5', '1', '9', '3', '8', '0', '2', '5', '0', '6', '4', '1', '3', '5', '9', '0', '6', '0', '5', '2', '3', '5', '4', '5', '6', '5', '7', '9', '5', '6', '7', '9', '1', '5', '7', '3', '9', '3', '7', '0', '0', '4', '3', '3', '7', '0', '4', '6', '1', '6', '8', '7', '2', '5', '2', '0', '7', '7', '9', '3', '8', '6', '7', '3', '6', '2', '0', '3', '3', '7', '0', '7', '5', '2', '6', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_jensenBoundDenominatorChars : List Char := ['6', '4', '5', '8', '3', '6', '7', '5', '9', '0', '6', '6', '2', '1', '4', '9', '2', '0', '4', '9', '5', '1', '0', '8', '0', '9', '8', '9', '8', '5', '2', '9', '2', '8', '5', '9', '5', '7', '9', '9', '9', '8', '6', '6', '7', '1', '5', '4', '7', '7', '5', '2', '9', '6', '9', '0', '3', '6', '9', '5', '5', '4', '5', '1', '1', '0', '6', '1', '1', '3', '6', '6', '6', '7', '6', '3', '2', '6', '3', '1', '1', '4', '6', '2', '7', '2', '0', '1', '8', '3', '8', '7', '8', '0', '9', '1', '3', '8', '0', '5', '5', '1', '9', '7', '5', '7', '8', '4', '4', '7', '5', '0', '6', '3']
noncomputable def geometryRow006_jensenBoundText : String := String.ofList (geometryRow006_jensenBoundNumeratorChars ++ '/' :: geometryRow006_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_jensenBound_before_field"
  err.flush

theorem geometryRow006_jensenBound_field :
    geometryRowsJson006.getObjVal? "jensen_bound" = .ok (.str geometryRow006_jensenBoundText) := by rfl

theorem geometryRow006_jensenBound_numerator_no_slash :
    geometryRow006_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow006_jensenBoundNumeratorChars = some (51938025064135906052354565795679157393700433704616872520779386736203370752614400000000000000000000 : Int) := by decide +kernel

theorem geometryRow006_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow006_jensenBoundDenominatorChars = some (645836759066214920495108098985292859579998667154775296903695545110611366676326311462720183878091380551975784475063 : Int) := by decide +kernel

theorem geometryRow006_jensenBound_denominator_nonzero : (645836759066214920495108098985292859579998667154775296903695545110611366676326311462720183878091380551975784475063 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_jensenBound_parse :
    parseRational geometryRow006_jensenBoundText = .ok geometryRowsTyped006.jensenBound :=
  original_rational_fraction_of_chars geometryRow006_jensenBoundNumeratorChars geometryRow006_jensenBoundDenominatorChars
    (51938025064135906052354565795679157393700433704616872520779386736203370752614400000000000000000000 : Int) (645836759066214920495108098985292859579998667154775296903695545110611366676326311462720183878091380551975784475063 : Int)
    geometryRow006_jensenBound_numerator_no_slash geometryRow006_jensenBound_numerator_parse
    geometryRow006_jensenBound_denominator_parse geometryRow006_jensenBound_denominator_nonzero

theorem geometryRow006_jensenBound_read :
    rationalField geometryRowsJson006 "jensen_bound" = .ok geometryRowsTyped006.jensenBound :=
  original_rationalField_of_string geometryRowsJson006 "jensen_bound" geometryRow006_jensenBoundText
    geometryRowsTyped006.jensenBound geometryRow006_jensenBound_field geometryRow006_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_factorMaxima_before"
  err.flush

theorem geometryRow006_factorMaxima_read :
    rationalArrayField geometryRowsJson006 "factor_maxima" = .ok geometryRowsTyped006.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_gapWeightedMeans_before"
  err.flush

theorem geometryRow006_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson006 "gap_weighted_means" = .ok geometryRowsTyped006.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow006_floorChars : List Char := ['6', '3', '7', '1', '5', '0', '8', '3', '3', '0', '3', '7', '2']
noncomputable def geometryRow006_floorText : String := String.ofList geometryRow006_floorChars

theorem geometryRow006_floor_text_read :
    geometryRowsJson006.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow006_floorText := by rfl

theorem geometryRow006_floor_chars_parse :
    SourceJson.intChars geometryRow006_floorChars = some (6371508330372 : Int) := by decide +kernel

theorem geometryRow006_floor_parse :
    parseInteger geometryRow006_floorText = .ok geometryRowsTyped006.jensenFloorQ96 := by
  simp only [geometryRow006_floorText, parseInteger, String.toList_ofList, geometryRow006_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_006 :
    decodeGeometryRow geometryRowsJson006 = .ok geometryRowsTyped006 :=
  original_geometryRow_of_fields geometryRowsJson006 geometryRowsTyped006 geometryRow006_floorText
    geometryRow006_simplexId_read geometryRow006_vertexIds_read
    geometryRow006_physicalVolume_read geometryRow006_meanGap_read
    geometryRow006_factorMaxima_read geometryRow006_gapWeightedMeans_read
    geometryRow006_jensenBound_read geometryRow006_floor_text_read geometryRow006_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_006_original_decoder_complete"
  err.flush

#print axioms geometryRow006_simplexId_read
#print axioms geometryRow006_vertexIds_read
#print axioms geometryRow006_physicalVolume_field
#print axioms geometryRow006_physicalVolume_numerator_no_slash
#print axioms geometryRow006_physicalVolume_numerator_parse
#print axioms geometryRow006_physicalVolume_denominator_parse
#print axioms geometryRow006_physicalVolume_denominator_nonzero
#print axioms geometryRow006_physicalVolume_parse
#print axioms geometryRow006_physicalVolume_read
#print axioms geometryRow006_meanGap_field
#print axioms geometryRow006_meanGap_numerator_no_slash
#print axioms geometryRow006_meanGap_numerator_parse
#print axioms geometryRow006_meanGap_denominator_parse
#print axioms geometryRow006_meanGap_denominator_nonzero
#print axioms geometryRow006_meanGap_parse
#print axioms geometryRow006_meanGap_read
#print axioms geometryRow006_jensenBound_field
#print axioms geometryRow006_jensenBound_numerator_no_slash
#print axioms geometryRow006_jensenBound_numerator_parse
#print axioms geometryRow006_jensenBound_denominator_parse
#print axioms geometryRow006_jensenBound_denominator_nonzero
#print axioms geometryRow006_jensenBound_parse
#print axioms geometryRow006_jensenBound_read
#print axioms geometryRow006_factorMaxima_read
#print axioms geometryRow006_gapWeightedMeans_read
#print axioms geometryRow006_floor_text_read
#print axioms geometryRow006_floor_chars_parse
#print axioms geometryRow006_floor_parse
#print axioms decode_geometry_Rows_006

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
