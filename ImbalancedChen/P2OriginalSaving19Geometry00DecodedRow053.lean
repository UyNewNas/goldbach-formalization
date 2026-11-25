import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01300

/-! Original GeometryRow 53: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson053 : SourceJson :=
  (simplicesChunk053Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped053 : GeometryRow :=
  { simplexId := 53,
    vertexIds := #[27, 26, 24, 22, 21, 19, 18, 3, 1],
    physicalVolume := ((767202232389881047226861111 : ℚ) / (58071715430400000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((146871 : ℚ) / (4000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((8578034581 : ℚ) / (95760000000 : ℚ)), ((8646924199 : ℚ) / (95760000000 : ℚ)), ((24206355611 : ℚ) / (191520000000 : ℚ)), ((18584716457 : ℚ) / (191520000000 : ℚ)), ((2457281071 : ℚ) / (27360000000 : ℚ)), ((12872666557 : ℚ) / (191520000000 : ℚ)), ((632155957 : ℚ) / (19152000000 : ℚ)), ((205400071 : ℚ) / (6384000000 : ℚ)), ((982932239 : ℚ) / (31920000000 : ℚ)), ((982930111 : ℚ) / (31920000000 : ℚ))],
    jensenBound := ((662466363172432087293004848099291924489170342730843291648000000000000000000000 : ℚ) / (18916080407880284506156517024149222290522730123758179000085209782015268895021026759026523962199 : ℚ)),
    jensenFloorQ96 := (2774675913293 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_simplexId_before"
  err.flush

theorem geometryRow053_simplexId_read :
    geometryRowsJson053.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped053.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_vertexIds_before"
  err.flush

theorem geometryRow053_vertexIds_read :
    geometryRowsJson053.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped053.vertexIds := by decide +kernel

noncomputable def geometryRow053_physicalVolumeNumeratorChars : List Char := ['7', '6', '7', '2', '0', '2', '2', '3', '2', '3', '8', '9', '8', '8', '1', '0', '4', '7', '2', '2', '6', '8', '6', '1', '1', '1', '1']
noncomputable def geometryRow053_physicalVolumeDenominatorChars : List Char := ['5', '8', '0', '7', '1', '7', '1', '5', '4', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_physicalVolumeText : String := String.ofList (geometryRow053_physicalVolumeNumeratorChars ++ '/' :: geometryRow053_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_physicalVolume_before_field"
  err.flush

theorem geometryRow053_physicalVolume_field :
    geometryRowsJson053.getObjVal? "physical_volume" = .ok (.str geometryRow053_physicalVolumeText) := by rfl

theorem geometryRow053_physicalVolume_numerator_no_slash :
    geometryRow053_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow053_physicalVolumeNumeratorChars = some (767202232389881047226861111 : Int) := by decide +kernel

theorem geometryRow053_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow053_physicalVolumeDenominatorChars = some (58071715430400000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow053_physicalVolume_denominator_nonzero : (58071715430400000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_physicalVolume_parse :
    parseRational geometryRow053_physicalVolumeText = .ok geometryRowsTyped053.physicalVolume :=
  original_rational_fraction_of_chars geometryRow053_physicalVolumeNumeratorChars geometryRow053_physicalVolumeDenominatorChars
    (767202232389881047226861111 : Int) (58071715430400000000000000000000000000000000000000000 : Int)
    geometryRow053_physicalVolume_numerator_no_slash geometryRow053_physicalVolume_numerator_parse
    geometryRow053_physicalVolume_denominator_parse geometryRow053_physicalVolume_denominator_nonzero

theorem geometryRow053_physicalVolume_read :
    rationalField geometryRowsJson053 "physical_volume" = .ok geometryRowsTyped053.physicalVolume :=
  original_rationalField_of_string geometryRowsJson053 "physical_volume" geometryRow053_physicalVolumeText
    geometryRowsTyped053.physicalVolume geometryRow053_physicalVolume_field geometryRow053_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_physicalVolume_complete"
  err.flush

noncomputable def geometryRow053_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow053_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_meanGapText : String := String.ofList (geometryRow053_meanGapNumeratorChars ++ '/' :: geometryRow053_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_meanGap_before_field"
  err.flush

theorem geometryRow053_meanGap_field :
    geometryRowsJson053.getObjVal? "mean_gap" = .ok (.str geometryRow053_meanGapText) := by rfl

theorem geometryRow053_meanGap_numerator_no_slash :
    geometryRow053_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_meanGap_numerator_parse :
    SourceJson.intChars geometryRow053_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow053_meanGap_denominator_parse :
    SourceJson.intChars geometryRow053_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow053_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_meanGap_parse :
    parseRational geometryRow053_meanGapText = .ok geometryRowsTyped053.meanGap :=
  original_rational_fraction_of_chars geometryRow053_meanGapNumeratorChars geometryRow053_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow053_meanGap_numerator_no_slash geometryRow053_meanGap_numerator_parse
    geometryRow053_meanGap_denominator_parse geometryRow053_meanGap_denominator_nonzero

theorem geometryRow053_meanGap_read :
    rationalField geometryRowsJson053 "mean_gap" = .ok geometryRowsTyped053.meanGap :=
  original_rationalField_of_string geometryRowsJson053 "mean_gap" geometryRow053_meanGapText
    geometryRowsTyped053.meanGap geometryRow053_meanGap_field geometryRow053_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_meanGap_complete"
  err.flush

noncomputable def geometryRow053_jensenBoundNumeratorChars : List Char := ['6', '6', '2', '4', '6', '6', '3', '6', '3', '1', '7', '2', '4', '3', '2', '0', '8', '7', '2', '9', '3', '0', '0', '4', '8', '4', '8', '0', '9', '9', '2', '9', '1', '9', '2', '4', '4', '8', '9', '1', '7', '0', '3', '4', '2', '7', '3', '0', '8', '4', '3', '2', '9', '1', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_jensenBoundDenominatorChars : List Char := ['1', '8', '9', '1', '6', '0', '8', '0', '4', '0', '7', '8', '8', '0', '2', '8', '4', '5', '0', '6', '1', '5', '6', '5', '1', '7', '0', '2', '4', '1', '4', '9', '2', '2', '2', '2', '9', '0', '5', '2', '2', '7', '3', '0', '1', '2', '3', '7', '5', '8', '1', '7', '9', '0', '0', '0', '0', '8', '5', '2', '0', '9', '7', '8', '2', '0', '1', '5', '2', '6', '8', '8', '9', '5', '0', '2', '1', '0', '2', '6', '7', '5', '9', '0', '2', '6', '5', '2', '3', '9', '6', '2', '1', '9', '9']
noncomputable def geometryRow053_jensenBoundText : String := String.ofList (geometryRow053_jensenBoundNumeratorChars ++ '/' :: geometryRow053_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_jensenBound_before_field"
  err.flush

theorem geometryRow053_jensenBound_field :
    geometryRowsJson053.getObjVal? "jensen_bound" = .ok (.str geometryRow053_jensenBoundText) := by rfl

theorem geometryRow053_jensenBound_numerator_no_slash :
    geometryRow053_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow053_jensenBoundNumeratorChars = some (662466363172432087293004848099291924489170342730843291648000000000000000000000 : Int) := by decide +kernel

theorem geometryRow053_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow053_jensenBoundDenominatorChars = some (18916080407880284506156517024149222290522730123758179000085209782015268895021026759026523962199 : Int) := by decide +kernel

theorem geometryRow053_jensenBound_denominator_nonzero : (18916080407880284506156517024149222290522730123758179000085209782015268895021026759026523962199 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_jensenBound_parse :
    parseRational geometryRow053_jensenBoundText = .ok geometryRowsTyped053.jensenBound :=
  original_rational_fraction_of_chars geometryRow053_jensenBoundNumeratorChars geometryRow053_jensenBoundDenominatorChars
    (662466363172432087293004848099291924489170342730843291648000000000000000000000 : Int) (18916080407880284506156517024149222290522730123758179000085209782015268895021026759026523962199 : Int)
    geometryRow053_jensenBound_numerator_no_slash geometryRow053_jensenBound_numerator_parse
    geometryRow053_jensenBound_denominator_parse geometryRow053_jensenBound_denominator_nonzero

theorem geometryRow053_jensenBound_read :
    rationalField geometryRowsJson053 "jensen_bound" = .ok geometryRowsTyped053.jensenBound :=
  original_rationalField_of_string geometryRowsJson053 "jensen_bound" geometryRow053_jensenBoundText
    geometryRowsTyped053.jensenBound geometryRow053_jensenBound_field geometryRow053_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_factorMaxima_before"
  err.flush

theorem geometryRow053_factorMaxima_read :
    rationalArrayField geometryRowsJson053 "factor_maxima" = .ok geometryRowsTyped053.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_gapWeightedMeans_before"
  err.flush

theorem geometryRow053_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson053 "gap_weighted_means" = .ok geometryRowsTyped053.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow053_floorChars : List Char := ['2', '7', '7', '4', '6', '7', '5', '9', '1', '3', '2', '9', '3']
noncomputable def geometryRow053_floorText : String := String.ofList geometryRow053_floorChars

theorem geometryRow053_floor_text_read :
    geometryRowsJson053.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow053_floorText := by rfl

theorem geometryRow053_floor_chars_parse :
    SourceJson.intChars geometryRow053_floorChars = some (2774675913293 : Int) := by decide +kernel

theorem geometryRow053_floor_parse :
    parseInteger geometryRow053_floorText = .ok geometryRowsTyped053.jensenFloorQ96 := by
  simp only [geometryRow053_floorText, parseInteger, String.toList_ofList, geometryRow053_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_053 :
    decodeGeometryRow geometryRowsJson053 = .ok geometryRowsTyped053 :=
  original_geometryRow_of_fields geometryRowsJson053 geometryRowsTyped053 geometryRow053_floorText
    geometryRow053_simplexId_read geometryRow053_vertexIds_read
    geometryRow053_physicalVolume_read geometryRow053_meanGap_read
    geometryRow053_factorMaxima_read geometryRow053_gapWeightedMeans_read
    geometryRow053_jensenBound_read geometryRow053_floor_text_read geometryRow053_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_053_original_decoder_complete"
  err.flush

#print axioms geometryRow053_simplexId_read
#print axioms geometryRow053_vertexIds_read
#print axioms geometryRow053_physicalVolume_field
#print axioms geometryRow053_physicalVolume_numerator_no_slash
#print axioms geometryRow053_physicalVolume_numerator_parse
#print axioms geometryRow053_physicalVolume_denominator_parse
#print axioms geometryRow053_physicalVolume_denominator_nonzero
#print axioms geometryRow053_physicalVolume_parse
#print axioms geometryRow053_physicalVolume_read
#print axioms geometryRow053_meanGap_field
#print axioms geometryRow053_meanGap_numerator_no_slash
#print axioms geometryRow053_meanGap_numerator_parse
#print axioms geometryRow053_meanGap_denominator_parse
#print axioms geometryRow053_meanGap_denominator_nonzero
#print axioms geometryRow053_meanGap_parse
#print axioms geometryRow053_meanGap_read
#print axioms geometryRow053_jensenBound_field
#print axioms geometryRow053_jensenBound_numerator_no_slash
#print axioms geometryRow053_jensenBound_numerator_parse
#print axioms geometryRow053_jensenBound_denominator_parse
#print axioms geometryRow053_jensenBound_denominator_nonzero
#print axioms geometryRow053_jensenBound_parse
#print axioms geometryRow053_jensenBound_read
#print axioms geometryRow053_factorMaxima_read
#print axioms geometryRow053_gapWeightedMeans_read
#print axioms geometryRow053_floor_text_read
#print axioms geometryRow053_floor_chars_parse
#print axioms geometryRow053_floor_parse
#print axioms decode_geometry_Rows_053

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
