import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00200

/-! Original GeometryRow 11: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson011 : SourceJson :=
  (simplicesChunk011Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped011 : GeometryRow :=
  { simplexId := 11,
    vertexIds := #[27, 25, 23, 21, 9, 5, 3, 1, 0],
    physicalVolume := ((4142617390083602941130318900376961 : ℚ) / (160414220285156250000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((1835396809313 : ℚ) / (19870200000000 : ℚ)), ((231211425631 : ℚ) / (2483775000000 : ℚ)), ((1619227229731 : ℚ) / (13246800000000 : ℚ)), ((406024547309 : ℚ) / (4415600000000 : ℚ)), ((75523585611 : ℚ) / (883120000000 : ℚ)), ((944589431549 : ℚ) / (13246800000000 : ℚ)), ((77120666101 : ℚ) / (2207800000000 : ℚ)), ((677531380637 : ℚ) / (19870200000000 : ℚ)), ((648472866467 : ℚ) / (19870200000000 : ℚ)), ((26264971399 : ℚ) / (827925000000 : ℚ))],
    jensenBound := ((166673417639041621371840701504491069997976762493159447528264447832706897018880000000000000000000000 : ℚ) / (2934067655757613586703679723667756183031567351645517409268572553778065594259814223412060128876804062431280607671787 : ℚ)),
    jensenFloorQ96 := (4500655802398 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_simplexId_before"
  err.flush

theorem geometryRow011_simplexId_read :
    geometryRowsJson011.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped011.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_vertexIds_before"
  err.flush

theorem geometryRow011_vertexIds_read :
    geometryRowsJson011.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped011.vertexIds := by decide +kernel

noncomputable def geometryRow011_physicalVolumeNumeratorChars : List Char := ['4', '1', '4', '2', '6', '1', '7', '3', '9', '0', '0', '8', '3', '6', '0', '2', '9', '4', '1', '1', '3', '0', '3', '1', '8', '9', '0', '0', '3', '7', '6', '9', '6', '1']
noncomputable def geometryRow011_physicalVolumeDenominatorChars : List Char := ['1', '6', '0', '4', '1', '4', '2', '2', '0', '2', '8', '5', '1', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_physicalVolumeText : String := String.ofList (geometryRow011_physicalVolumeNumeratorChars ++ '/' :: geometryRow011_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_physicalVolume_before_field"
  err.flush

theorem geometryRow011_physicalVolume_field :
    geometryRowsJson011.getObjVal? "physical_volume" = .ok (.str geometryRow011_physicalVolumeText) := by rfl

theorem geometryRow011_physicalVolume_numerator_no_slash :
    geometryRow011_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow011_physicalVolumeNumeratorChars = some (4142617390083602941130318900376961 : Int) := by decide +kernel

theorem geometryRow011_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow011_physicalVolumeDenominatorChars = some (160414220285156250000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow011_physicalVolume_denominator_nonzero : (160414220285156250000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_physicalVolume_parse :
    parseRational geometryRow011_physicalVolumeText = .ok geometryRowsTyped011.physicalVolume :=
  original_rational_fraction_of_chars geometryRow011_physicalVolumeNumeratorChars geometryRow011_physicalVolumeDenominatorChars
    (4142617390083602941130318900376961 : Int) (160414220285156250000000000000000000000000000000000000000000 : Int)
    geometryRow011_physicalVolume_numerator_no_slash geometryRow011_physicalVolume_numerator_parse
    geometryRow011_physicalVolume_denominator_parse geometryRow011_physicalVolume_denominator_nonzero

theorem geometryRow011_physicalVolume_read :
    rationalField geometryRowsJson011 "physical_volume" = .ok geometryRowsTyped011.physicalVolume :=
  original_rationalField_of_string geometryRowsJson011 "physical_volume" geometryRow011_physicalVolumeText
    geometryRowsTyped011.physicalVolume geometryRow011_physicalVolume_field geometryRow011_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_physicalVolume_complete"
  err.flush

noncomputable def geometryRow011_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow011_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_meanGapText : String := String.ofList (geometryRow011_meanGapNumeratorChars ++ '/' :: geometryRow011_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_meanGap_before_field"
  err.flush

theorem geometryRow011_meanGap_field :
    geometryRowsJson011.getObjVal? "mean_gap" = .ok (.str geometryRow011_meanGapText) := by rfl

theorem geometryRow011_meanGap_numerator_no_slash :
    geometryRow011_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_meanGap_numerator_parse :
    SourceJson.intChars geometryRow011_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow011_meanGap_denominator_parse :
    SourceJson.intChars geometryRow011_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow011_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_meanGap_parse :
    parseRational geometryRow011_meanGapText = .ok geometryRowsTyped011.meanGap :=
  original_rational_fraction_of_chars geometryRow011_meanGapNumeratorChars geometryRow011_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow011_meanGap_numerator_no_slash geometryRow011_meanGap_numerator_parse
    geometryRow011_meanGap_denominator_parse geometryRow011_meanGap_denominator_nonzero

theorem geometryRow011_meanGap_read :
    rationalField geometryRowsJson011 "mean_gap" = .ok geometryRowsTyped011.meanGap :=
  original_rationalField_of_string geometryRowsJson011 "mean_gap" geometryRow011_meanGapText
    geometryRowsTyped011.meanGap geometryRow011_meanGap_field geometryRow011_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_meanGap_complete"
  err.flush

noncomputable def geometryRow011_jensenBoundNumeratorChars : List Char := ['1', '6', '6', '6', '7', '3', '4', '1', '7', '6', '3', '9', '0', '4', '1', '6', '2', '1', '3', '7', '1', '8', '4', '0', '7', '0', '1', '5', '0', '4', '4', '9', '1', '0', '6', '9', '9', '9', '7', '9', '7', '6', '7', '6', '2', '4', '9', '3', '1', '5', '9', '4', '4', '7', '5', '2', '8', '2', '6', '4', '4', '4', '7', '8', '3', '2', '7', '0', '6', '8', '9', '7', '0', '1', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_jensenBoundDenominatorChars : List Char := ['2', '9', '3', '4', '0', '6', '7', '6', '5', '5', '7', '5', '7', '6', '1', '3', '5', '8', '6', '7', '0', '3', '6', '7', '9', '7', '2', '3', '6', '6', '7', '7', '5', '6', '1', '8', '3', '0', '3', '1', '5', '6', '7', '3', '5', '1', '6', '4', '5', '5', '1', '7', '4', '0', '9', '2', '6', '8', '5', '7', '2', '5', '5', '3', '7', '7', '8', '0', '6', '5', '5', '9', '4', '2', '5', '9', '8', '1', '4', '2', '2', '3', '4', '1', '2', '0', '6', '0', '1', '2', '8', '8', '7', '6', '8', '0', '4', '0', '6', '2', '4', '3', '1', '2', '8', '0', '6', '0', '7', '6', '7', '1', '7', '8', '7']
noncomputable def geometryRow011_jensenBoundText : String := String.ofList (geometryRow011_jensenBoundNumeratorChars ++ '/' :: geometryRow011_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_jensenBound_before_field"
  err.flush

theorem geometryRow011_jensenBound_field :
    geometryRowsJson011.getObjVal? "jensen_bound" = .ok (.str geometryRow011_jensenBoundText) := by rfl

theorem geometryRow011_jensenBound_numerator_no_slash :
    geometryRow011_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow011_jensenBoundNumeratorChars = some (166673417639041621371840701504491069997976762493159447528264447832706897018880000000000000000000000 : Int) := by decide +kernel

theorem geometryRow011_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow011_jensenBoundDenominatorChars = some (2934067655757613586703679723667756183031567351645517409268572553778065594259814223412060128876804062431280607671787 : Int) := by decide +kernel

theorem geometryRow011_jensenBound_denominator_nonzero : (2934067655757613586703679723667756183031567351645517409268572553778065594259814223412060128876804062431280607671787 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_jensenBound_parse :
    parseRational geometryRow011_jensenBoundText = .ok geometryRowsTyped011.jensenBound :=
  original_rational_fraction_of_chars geometryRow011_jensenBoundNumeratorChars geometryRow011_jensenBoundDenominatorChars
    (166673417639041621371840701504491069997976762493159447528264447832706897018880000000000000000000000 : Int) (2934067655757613586703679723667756183031567351645517409268572553778065594259814223412060128876804062431280607671787 : Int)
    geometryRow011_jensenBound_numerator_no_slash geometryRow011_jensenBound_numerator_parse
    geometryRow011_jensenBound_denominator_parse geometryRow011_jensenBound_denominator_nonzero

theorem geometryRow011_jensenBound_read :
    rationalField geometryRowsJson011 "jensen_bound" = .ok geometryRowsTyped011.jensenBound :=
  original_rationalField_of_string geometryRowsJson011 "jensen_bound" geometryRow011_jensenBoundText
    geometryRowsTyped011.jensenBound geometryRow011_jensenBound_field geometryRow011_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_factorMaxima_before"
  err.flush

theorem geometryRow011_factorMaxima_read :
    rationalArrayField geometryRowsJson011 "factor_maxima" = .ok geometryRowsTyped011.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_gapWeightedMeans_before"
  err.flush

theorem geometryRow011_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson011 "gap_weighted_means" = .ok geometryRowsTyped011.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow011_floorChars : List Char := ['4', '5', '0', '0', '6', '5', '5', '8', '0', '2', '3', '9', '8']
noncomputable def geometryRow011_floorText : String := String.ofList geometryRow011_floorChars

theorem geometryRow011_floor_text_read :
    geometryRowsJson011.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow011_floorText := by rfl

theorem geometryRow011_floor_chars_parse :
    SourceJson.intChars geometryRow011_floorChars = some (4500655802398 : Int) := by decide +kernel

theorem geometryRow011_floor_parse :
    parseInteger geometryRow011_floorText = .ok geometryRowsTyped011.jensenFloorQ96 := by
  simp only [geometryRow011_floorText, parseInteger, String.toList_ofList, geometryRow011_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_011 :
    decodeGeometryRow geometryRowsJson011 = .ok geometryRowsTyped011 :=
  original_geometryRow_of_fields geometryRowsJson011 geometryRowsTyped011 geometryRow011_floorText
    geometryRow011_simplexId_read geometryRow011_vertexIds_read
    geometryRow011_physicalVolume_read geometryRow011_meanGap_read
    geometryRow011_factorMaxima_read geometryRow011_gapWeightedMeans_read
    geometryRow011_jensenBound_read geometryRow011_floor_text_read geometryRow011_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_011_original_decoder_complete"
  err.flush

#print axioms geometryRow011_simplexId_read
#print axioms geometryRow011_vertexIds_read
#print axioms geometryRow011_physicalVolume_field
#print axioms geometryRow011_physicalVolume_numerator_no_slash
#print axioms geometryRow011_physicalVolume_numerator_parse
#print axioms geometryRow011_physicalVolume_denominator_parse
#print axioms geometryRow011_physicalVolume_denominator_nonzero
#print axioms geometryRow011_physicalVolume_parse
#print axioms geometryRow011_physicalVolume_read
#print axioms geometryRow011_meanGap_field
#print axioms geometryRow011_meanGap_numerator_no_slash
#print axioms geometryRow011_meanGap_numerator_parse
#print axioms geometryRow011_meanGap_denominator_parse
#print axioms geometryRow011_meanGap_denominator_nonzero
#print axioms geometryRow011_meanGap_parse
#print axioms geometryRow011_meanGap_read
#print axioms geometryRow011_jensenBound_field
#print axioms geometryRow011_jensenBound_numerator_no_slash
#print axioms geometryRow011_jensenBound_numerator_parse
#print axioms geometryRow011_jensenBound_denominator_parse
#print axioms geometryRow011_jensenBound_denominator_nonzero
#print axioms geometryRow011_jensenBound_parse
#print axioms geometryRow011_jensenBound_read
#print axioms geometryRow011_factorMaxima_read
#print axioms geometryRow011_gapWeightedMeans_read
#print axioms geometryRow011_floor_text_read
#print axioms geometryRow011_floor_chars_parse
#print axioms geometryRow011_floor_parse
#print axioms decode_geometry_Rows_011

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
