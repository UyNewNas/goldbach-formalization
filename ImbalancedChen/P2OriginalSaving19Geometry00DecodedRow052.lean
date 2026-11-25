import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01300

/-! Original GeometryRow 52: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson052 : SourceJson :=
  (simplicesChunk052Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped052 : GeometryRow :=
  { simplexId := 52,
    vertexIds := #[27, 26, 24, 22, 21, 19, 5, 3, 1],
    physicalVolume := ((1837083272007579570119259708653 : ℚ) / (130827278905344000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((720456431561 : ℚ) / (7948080000000 : ℚ)), ((145234853971 : ℚ) / (1589616000000 : ℚ)), ((1992813408913 : ℚ) / (15896160000000 : ℚ)), ((1520564318239 : ℚ) / (15896160000000 : ℚ)), ((39963781141 : ℚ) / (454176000000 : ℚ)), ((1079509820063 : ℚ) / (15896160000000 : ℚ)), ((268661649913 : ℚ) / (7948080000000 : ℚ)), ((87346672051 : ℚ) / (2649360000000 : ℚ)), ((82525549319 : ℚ) / (2649360000000 : ℚ)), ((5501691513 : ℚ) / (176624000000 : ℚ))],
    jensenBound := ((566492753135926867605697131505497600332379699614493463148247530236148208107520000000000000000000 : ℚ) / (16193374737381552658525489553687457810026693619244431490202811827599368435557515501402284122588513916714172509419 : ℚ)),
    jensenFloorQ96 := (2771638440812 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_simplexId_before"
  err.flush

theorem geometryRow052_simplexId_read :
    geometryRowsJson052.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped052.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_vertexIds_before"
  err.flush

theorem geometryRow052_vertexIds_read :
    geometryRowsJson052.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped052.vertexIds := by decide +kernel

noncomputable def geometryRow052_physicalVolumeNumeratorChars : List Char := ['1', '8', '3', '7', '0', '8', '3', '2', '7', '2', '0', '0', '7', '5', '7', '9', '5', '7', '0', '1', '1', '9', '2', '5', '9', '7', '0', '8', '6', '5', '3']
noncomputable def geometryRow052_physicalVolumeDenominatorChars : List Char := ['1', '3', '0', '8', '2', '7', '2', '7', '8', '9', '0', '5', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_physicalVolumeText : String := String.ofList (geometryRow052_physicalVolumeNumeratorChars ++ '/' :: geometryRow052_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_physicalVolume_before_field"
  err.flush

theorem geometryRow052_physicalVolume_field :
    geometryRowsJson052.getObjVal? "physical_volume" = .ok (.str geometryRow052_physicalVolumeText) := by rfl

theorem geometryRow052_physicalVolume_numerator_no_slash :
    geometryRow052_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow052_physicalVolumeNumeratorChars = some (1837083272007579570119259708653 : Int) := by decide +kernel

theorem geometryRow052_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow052_physicalVolumeDenominatorChars = some (130827278905344000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow052_physicalVolume_denominator_nonzero : (130827278905344000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_physicalVolume_parse :
    parseRational geometryRow052_physicalVolumeText = .ok geometryRowsTyped052.physicalVolume :=
  original_rational_fraction_of_chars geometryRow052_physicalVolumeNumeratorChars geometryRow052_physicalVolumeDenominatorChars
    (1837083272007579570119259708653 : Int) (130827278905344000000000000000000000000000000000000000000 : Int)
    geometryRow052_physicalVolume_numerator_no_slash geometryRow052_physicalVolume_numerator_parse
    geometryRow052_physicalVolume_denominator_parse geometryRow052_physicalVolume_denominator_nonzero

theorem geometryRow052_physicalVolume_read :
    rationalField geometryRowsJson052 "physical_volume" = .ok geometryRowsTyped052.physicalVolume :=
  original_rationalField_of_string geometryRowsJson052 "physical_volume" geometryRow052_physicalVolumeText
    geometryRowsTyped052.physicalVolume geometryRow052_physicalVolume_field geometryRow052_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_physicalVolume_complete"
  err.flush

noncomputable def geometryRow052_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow052_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_meanGapText : String := String.ofList (geometryRow052_meanGapNumeratorChars ++ '/' :: geometryRow052_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_meanGap_before_field"
  err.flush

theorem geometryRow052_meanGap_field :
    geometryRowsJson052.getObjVal? "mean_gap" = .ok (.str geometryRow052_meanGapText) := by rfl

theorem geometryRow052_meanGap_numerator_no_slash :
    geometryRow052_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_meanGap_numerator_parse :
    SourceJson.intChars geometryRow052_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow052_meanGap_denominator_parse :
    SourceJson.intChars geometryRow052_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow052_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_meanGap_parse :
    parseRational geometryRow052_meanGapText = .ok geometryRowsTyped052.meanGap :=
  original_rational_fraction_of_chars geometryRow052_meanGapNumeratorChars geometryRow052_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow052_meanGap_numerator_no_slash geometryRow052_meanGap_numerator_parse
    geometryRow052_meanGap_denominator_parse geometryRow052_meanGap_denominator_nonzero

theorem geometryRow052_meanGap_read :
    rationalField geometryRowsJson052 "mean_gap" = .ok geometryRowsTyped052.meanGap :=
  original_rationalField_of_string geometryRowsJson052 "mean_gap" geometryRow052_meanGapText
    geometryRowsTyped052.meanGap geometryRow052_meanGap_field geometryRow052_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_meanGap_complete"
  err.flush

noncomputable def geometryRow052_jensenBoundNumeratorChars : List Char := ['5', '6', '6', '4', '9', '2', '7', '5', '3', '1', '3', '5', '9', '2', '6', '8', '6', '7', '6', '0', '5', '6', '9', '7', '1', '3', '1', '5', '0', '5', '4', '9', '7', '6', '0', '0', '3', '3', '2', '3', '7', '9', '6', '9', '9', '6', '1', '4', '4', '9', '3', '4', '6', '3', '1', '4', '8', '2', '4', '7', '5', '3', '0', '2', '3', '6', '1', '4', '8', '2', '0', '8', '1', '0', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_jensenBoundDenominatorChars : List Char := ['1', '6', '1', '9', '3', '3', '7', '4', '7', '3', '7', '3', '8', '1', '5', '5', '2', '6', '5', '8', '5', '2', '5', '4', '8', '9', '5', '5', '3', '6', '8', '7', '4', '5', '7', '8', '1', '0', '0', '2', '6', '6', '9', '3', '6', '1', '9', '2', '4', '4', '4', '3', '1', '4', '9', '0', '2', '0', '2', '8', '1', '1', '8', '2', '7', '5', '9', '9', '3', '6', '8', '4', '3', '5', '5', '5', '7', '5', '1', '5', '5', '0', '1', '4', '0', '2', '2', '8', '4', '1', '2', '2', '5', '8', '8', '5', '1', '3', '9', '1', '6', '7', '1', '4', '1', '7', '2', '5', '0', '9', '4', '1', '9']
noncomputable def geometryRow052_jensenBoundText : String := String.ofList (geometryRow052_jensenBoundNumeratorChars ++ '/' :: geometryRow052_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_jensenBound_before_field"
  err.flush

theorem geometryRow052_jensenBound_field :
    geometryRowsJson052.getObjVal? "jensen_bound" = .ok (.str geometryRow052_jensenBoundText) := by rfl

theorem geometryRow052_jensenBound_numerator_no_slash :
    geometryRow052_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow052_jensenBoundNumeratorChars = some (566492753135926867605697131505497600332379699614493463148247530236148208107520000000000000000000 : Int) := by decide +kernel

theorem geometryRow052_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow052_jensenBoundDenominatorChars = some (16193374737381552658525489553687457810026693619244431490202811827599368435557515501402284122588513916714172509419 : Int) := by decide +kernel

theorem geometryRow052_jensenBound_denominator_nonzero : (16193374737381552658525489553687457810026693619244431490202811827599368435557515501402284122588513916714172509419 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_jensenBound_parse :
    parseRational geometryRow052_jensenBoundText = .ok geometryRowsTyped052.jensenBound :=
  original_rational_fraction_of_chars geometryRow052_jensenBoundNumeratorChars geometryRow052_jensenBoundDenominatorChars
    (566492753135926867605697131505497600332379699614493463148247530236148208107520000000000000000000 : Int) (16193374737381552658525489553687457810026693619244431490202811827599368435557515501402284122588513916714172509419 : Int)
    geometryRow052_jensenBound_numerator_no_slash geometryRow052_jensenBound_numerator_parse
    geometryRow052_jensenBound_denominator_parse geometryRow052_jensenBound_denominator_nonzero

theorem geometryRow052_jensenBound_read :
    rationalField geometryRowsJson052 "jensen_bound" = .ok geometryRowsTyped052.jensenBound :=
  original_rationalField_of_string geometryRowsJson052 "jensen_bound" geometryRow052_jensenBoundText
    geometryRowsTyped052.jensenBound geometryRow052_jensenBound_field geometryRow052_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_factorMaxima_before"
  err.flush

theorem geometryRow052_factorMaxima_read :
    rationalArrayField geometryRowsJson052 "factor_maxima" = .ok geometryRowsTyped052.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_gapWeightedMeans_before"
  err.flush

theorem geometryRow052_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson052 "gap_weighted_means" = .ok geometryRowsTyped052.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow052_floorChars : List Char := ['2', '7', '7', '1', '6', '3', '8', '4', '4', '0', '8', '1', '2']
noncomputable def geometryRow052_floorText : String := String.ofList geometryRow052_floorChars

theorem geometryRow052_floor_text_read :
    geometryRowsJson052.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow052_floorText := by rfl

theorem geometryRow052_floor_chars_parse :
    SourceJson.intChars geometryRow052_floorChars = some (2771638440812 : Int) := by decide +kernel

theorem geometryRow052_floor_parse :
    parseInteger geometryRow052_floorText = .ok geometryRowsTyped052.jensenFloorQ96 := by
  simp only [geometryRow052_floorText, parseInteger, String.toList_ofList, geometryRow052_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_052 :
    decodeGeometryRow geometryRowsJson052 = .ok geometryRowsTyped052 :=
  original_geometryRow_of_fields geometryRowsJson052 geometryRowsTyped052 geometryRow052_floorText
    geometryRow052_simplexId_read geometryRow052_vertexIds_read
    geometryRow052_physicalVolume_read geometryRow052_meanGap_read
    geometryRow052_factorMaxima_read geometryRow052_gapWeightedMeans_read
    geometryRow052_jensenBound_read geometryRow052_floor_text_read geometryRow052_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_052_original_decoder_complete"
  err.flush

#print axioms geometryRow052_simplexId_read
#print axioms geometryRow052_vertexIds_read
#print axioms geometryRow052_physicalVolume_field
#print axioms geometryRow052_physicalVolume_numerator_no_slash
#print axioms geometryRow052_physicalVolume_numerator_parse
#print axioms geometryRow052_physicalVolume_denominator_parse
#print axioms geometryRow052_physicalVolume_denominator_nonzero
#print axioms geometryRow052_physicalVolume_parse
#print axioms geometryRow052_physicalVolume_read
#print axioms geometryRow052_meanGap_field
#print axioms geometryRow052_meanGap_numerator_no_slash
#print axioms geometryRow052_meanGap_numerator_parse
#print axioms geometryRow052_meanGap_denominator_parse
#print axioms geometryRow052_meanGap_denominator_nonzero
#print axioms geometryRow052_meanGap_parse
#print axioms geometryRow052_meanGap_read
#print axioms geometryRow052_jensenBound_field
#print axioms geometryRow052_jensenBound_numerator_no_slash
#print axioms geometryRow052_jensenBound_numerator_parse
#print axioms geometryRow052_jensenBound_denominator_parse
#print axioms geometryRow052_jensenBound_denominator_nonzero
#print axioms geometryRow052_jensenBound_parse
#print axioms geometryRow052_jensenBound_read
#print axioms geometryRow052_factorMaxima_read
#print axioms geometryRow052_gapWeightedMeans_read
#print axioms geometryRow052_floor_text_read
#print axioms geometryRow052_floor_chars_parse
#print axioms geometryRow052_floor_parse
#print axioms decode_geometry_Rows_052

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
